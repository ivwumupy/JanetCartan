module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.SymbolRegularity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.SchwartzSlices

/-!
# Bounded realization of the fixed scalar physical multiplier

The real scalar symbol acts in physical covectors; Mathlib's Fourier
transform is evaluated with the explicit `2π` conversion. The construction
uses the existing vector multiplication operator and Fourier isometry.
Consumer: realization of the full terminal `AΓ-I` in
`app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Filter
open scoped ContDiff ComplexInnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds LowBounds.FrequencyCutoff
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The bounded real scalar physical-frequency multiplier, retaining the
original symbol and its entire low-frequency modification. It is fixed
before any localization accuracy (`app:ch_regular:eq:chain-tail`). -/
def scalarPhysicalFrequencyOperator (b : E → ℝ) (hb : Continuous b)
    (hbound : ∀ ξ, ‖b ξ‖ ≤ 1) : H →L[ℂ] H :=
  (fourierInvCLM ℂ H).comp
    ((sourceCutMultiplier (fun ξ ↦ b ((2 * Real.pi) • ξ))
      (hb.comp (by fun_prop))
      (fun ξ ↦ hbound ((2 * Real.pi) • ξ))).comp (fourierCLM ℂ H))

/-- Plancherel bounds the original scalar multiplier on the same Euclidean
vector L² space, without a frequency-support hypothesis on the datum.
Consumer: terminal physical realization (`resolved-angular-tail`). -/
theorem norm_scalarPhysicalFrequencyOperator_le (b : E → ℝ) (hb : Continuous b)
    (hbound : ∀ ξ, ‖b ξ‖ ≤ 1) :
    ‖scalarPhysicalFrequencyOperator (r := r) b hb hbound‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(Lp.fourierTransformₗᵢ E V).symm
    (sourceCutMultiplier (fun ξ ↦ b ((2 * Real.pi) • ξ))
      (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ)) (𝓕 u))‖ ≤ 1 * ‖u‖
  rw [LinearIsometryEquiv.norm_map, ← Lp.norm_fourier_eq u]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sourceCutMultiplier_le _ _ _) (norm_nonneg _))

/-- The literal Hilbert adjoint of the real fixed multiplier is itself.
Consumer: reversed physical masks in the terminal defect, as required by
`app:ch_regular:lem:finite-chain`. -/
theorem scalarPhysicalFrequencyOperator_adjoint (b : E → ℝ) (hb : Continuous b)
    (hbound : ∀ ξ, ‖b ξ‖ ≤ 1) :
    (scalarPhysicalFrequencyOperator (r := r) b hb hbound).adjoint =
      scalarPhysicalFrequencyOperator b hb hbound := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro u v
  change ⟪scalarPhysicalFrequencyOperator b hb hbound u, v⟫ =
    ⟪u, scalarPhysicalFrequencyOperator b hb hbound v⟫
  rw [← Lp.inner_fourier_eq (scalarPhysicalFrequencyOperator b hb hbound u) v,
    ← Lp.inner_fourier_eq u (scalarPhysicalFrequencyOperator b hb hbound v)]
  let B := sourceCutMultiplier (r := r) (fun ξ ↦ b ((2 * Real.pi) • ξ))
    (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ))
  change ⟪𝓕 (𝓕⁻ (B (𝓕 u))), 𝓕 v⟫ = ⟪𝓕 u, 𝓕 (𝓕⁻ (B (𝓕 v)))⟫
  simp only [fourier_fourierInv_eq]
  dsimp only [B]
  rw [← ContinuousLinearMap.adjoint_inner_left, sourceCutMultiplier_adjoint]

/-- The bounded construction agrees with the existing physical Schwartz
multiplier, with no norm-equivalence factor or altered Fourier convention.
The temperate-growth producer for the actual finite symbol is
`actualFamily_angularSymbol_hasTemperateGrowth`. Consumer: bounded terminal
PDO identification (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem scalarPhysicalFrequencyOperator_toEuclideanSchwartz
    (b : E → ℝ) (hb : Continuous b) (hbound : ∀ ξ, ‖b ξ‖ ≤ 1)
    (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (g : SchwartzMap E (Fin r → ℂ)) :
    scalarPhysicalFrequencyOperator b hb hbound ((toEuclideanSchwartz g).toLp 2) =
      (toEuclideanSchwartz (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g)).toLp 2 := by
  have hbc : (fun ξ : E ↦ (b ((2 * Real.pi) • ξ) : ℂ)).HasTemperateGrowth :=
    ht.comp (by fun_prop)
  apply (Lp.fourierTransformₗᵢ E V).injective
  change 𝓕 (𝓕⁻ (sourceCutMultiplier (fun ξ ↦ b ((2 * Real.pi) • ξ))
    (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ))
    (𝓕 ((toEuclideanSchwartz g).toLp 2)))) =
    𝓕 ((toEuclideanSchwartz (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g)).toLp 2)
  rw [fourier_fourierInv_eq, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq, ← toEuclideanSchwartz_fourier,
    ← toEuclideanSchwartz_fourier]
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn
    (fun ξ ↦ b ((2 * Real.pi) • ξ)) _ _ ((toEuclideanSchwartz (𝓕 g)).toLp 2),
    (toEuclideanSchwartz (𝓕 g)).coeFn_toLp 2,
    (toEuclideanSchwartz (𝓕 (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g))).coeFn_toLp 2]
    with ξ hm hg ho
  rw [hm, hg, ho]
  simp only [physicalMultiplier, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, toEuclideanSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply_apply hbc]
  rfl

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
