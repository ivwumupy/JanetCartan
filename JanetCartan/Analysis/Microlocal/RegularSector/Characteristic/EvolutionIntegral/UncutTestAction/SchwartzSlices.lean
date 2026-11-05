module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Uncut physical multipliers and their Schwartz restrictions

The multiplier is Mathlib's existing Fourier multiplier evaluated at physical
covectors. Its spatial and temporal restrictions are actual Schwartz functions.
These constructions are consumed by the uncut Fourier splitting in
`app:ch_regular_base:eq:fixed-time-representation`.

The `HasTemperateGrowth` input describes the original multiplier symbol, not
the desired operator action. An order-zero symbol supplies it through bounds
on every derivative; a single finite low-operator reserve alone does not.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification SymbolBudgets
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

private def timeSpaceInsertion : (ℝ × Euclidean d) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ timeSpacePoint p.1 p.2
      map_add' := by
        intro p z
        ext i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      map_smul' := by
        intro a p
        ext i
        exact Fin.cases rfl (fun _ ↦ rfl) i }

/-- Affine insertion of a fixed time has temperate growth. Consumer:
`spatialSchwartzSlice`, in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem hasTemperateGrowth_timeSpacePoint_fixedTime (s : ℝ) :
    (fun y : Euclidean d ↦ timeSpacePoint s y).HasTemperateGrowth := by
  simpa [Function.comp_def, timeSpaceInsertion] using timeSpaceInsertion.hasTemperateGrowth.comp
    (((ContinuousLinearMap.inl ℝ ℝ (Euclidean d)).hasTemperateGrowth.comp
      (Function.HasTemperateGrowth.const s)).add
        (ContinuousLinearMap.inr ℝ ℝ (Euclidean d)).hasTemperateGrowth)

/-- Affine insertion of a fixed spatial covector has temperate growth.
Consumer: integrability on every temporal fiber in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem hasTemperateGrowth_timeSpacePoint_fixedSpace (η : Euclidean d) :
    (fun τ : ℝ ↦ timeSpacePoint τ η).HasTemperateGrowth := by
  simpa [Function.comp_def, timeSpaceInsertion] using timeSpaceInsertion.hasTemperateGrowth.comp
    ((ContinuousLinearMap.inl ℝ ℝ (Euclidean d)).hasTemperateGrowth.add
      ((ContinuousLinearMap.inr ℝ ℝ (Euclidean d)).hasTemperateGrowth.comp
        (Function.HasTemperateGrowth.const η)))

/-- Restricting a spacetime Schwartz function to a fixed time produces an
actual spatial Schwartz function. Consumer: `physicalMultiplierSlice`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
def spatialSchwartzSlice (f : SchwartzMap E V) (s : ℝ) :
    SchwartzMap (Euclidean d) V :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_timeSpacePoint_fixedTime s)
    ⟨1, 1, fun y ↦ by
      simpa using (norm_spatialPart_le (timeSpacePoint s y)).trans
        (le_add_of_nonneg_left (by positivity))⟩ f

/-- The spatial Schwartz restriction retains the original coordinates in
`app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem spatialSchwartzSlice_apply (f : SchwartzMap E V)
    (s : ℝ) (y : Euclidean d) :
    spatialSchwartzSlice f s y = f (timeSpacePoint s y) := rfl

/-- Restricting a Schwartz frequency datum to a temporal line is Schwartz.
Consumer: absolute convergence of the temporal inverse Fourier integral in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def temporalSchwartzFiber (f : SchwartzMap E V) (η : Euclidean d) :
    SchwartzMap ℝ V :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_timeSpacePoint_fixedSpace η)
    ⟨1, 1, fun τ ↦ by
      simpa using (PiLp.norm_apply_le (timeSpacePoint τ η) 0).trans
        (le_add_of_nonneg_left (by positivity))⟩ f

/-- The temporal Schwartz restriction is the literal frequency fiber in
`app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem temporalSchwartzFiber_apply (f : SchwartzMap E V)
    (η : Euclidean d) (τ : ℝ) :
    temporalSchwartzFiber f η τ = f (timeSpacePoint τ η) := rfl

/-- The original uncut vector multiplier, reusing Mathlib's multiplier and
rescaling its frequency argument to physical covectors. Consumer: the original
`Bβ` in `app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalMultiplier (β : E → ℂ) (v : SchwartzMap E V) : SchwartzMap E V :=
  SchwartzMap.fourierMultiplierCLM V (fun ξ ↦ β ((2 * Real.pi) • ξ)) v

/-- The rescaled existing multiplier equals physical Fourier inversion of
the original, uncut frequency datum. No cutoff is inserted in this identity.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalMultiplier_eq_physicalInverse (β : E → ℂ)
    (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V) :
    physicalMultiplier β v = physicalInverseSchwartz
      (SchwartzMap.smulLeftCLM V β (sourceInputFourierTransform v)) := by
  have hscaled : (fun ξ ↦ β ((2 * Real.pi) • ξ)).HasTemperateGrowth :=
    hβ.comp (by fun_prop)
  unfold physicalMultiplier SchwartzMap.fourierMultiplierCLM
  change 𝓕⁻ (SchwartzMap.smulLeftCLM V (fun ξ ↦ β ((2 * Real.pi) • ξ)) (𝓕 v)) = _
  unfold physicalInverseSchwartz
  congr 1
  apply SchwartzMap.ext
  intro ξ
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, SchwartzMap.smulLeftCLM_apply_apply hscaled,
    SchwartzMap.smulLeftCLM_apply_apply hβ]
  change β ((2 * Real.pi) • ξ) • (𝓕 v) ξ =
    β ((2 * Real.pi) • ξ) • (𝓕 v) ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ))
  rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- The uncut multiplier has the literal inverse physical Fourier integral,
with exactly `(2π)⁻⁽ᵈ⁺¹⁾`. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalMultiplier_eq_integral (β : E → ℂ)
    (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V) (x : E) :
    physicalMultiplier β v x = ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        (β ξ • sourceInputFourierTransform v ξ) := by
  rw [physicalMultiplier_eq_physicalInverse β hβ,
    physicalInverseSchwartz_eq_integral]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hβ]

/-- The physical Fourier transform of the uncut multiplier is exactly the
original symbol times the source transform. Consumer: uncut multiplier-slice
identification in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_physicalMultiplier (β : E → ℂ)
    (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V) (ξ : E) :
    sourceInputFourierTransform (physicalMultiplier β v) ξ =
      β ξ • sourceInputFourierTransform v ξ := by
  rw [physicalMultiplier_eq_physicalInverse β hβ,
    sourceInputFourierTransform_physicalInverseSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply hβ]

/-- The actual spatial slice of the uncut multiplier. It is Schwartz by
restriction, rather than by a postulated slice identity. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalMultiplierSlice (β : E → ℂ) (v : SchwartzMap E V) (s : ℝ) :
    SchwartzMap (Euclidean d) V :=
  spatialSchwartzSlice (physicalMultiplier β v) s

/-- The uncut spatial slice agrees pointwise with the spacetime multiplier
in `app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem physicalMultiplierSlice_apply (β : E → ℂ)
    (v : SchwartzMap E V) (s : ℝ) (y : Euclidean d) :
    physicalMultiplierSlice β v s y = physicalMultiplier β v (timeSpacePoint s y) := rfl

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
