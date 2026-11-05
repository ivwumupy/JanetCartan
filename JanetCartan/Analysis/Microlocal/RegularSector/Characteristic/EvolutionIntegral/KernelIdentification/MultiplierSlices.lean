module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices.Inversion
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices.TemporalSchwartz

/-!
# Physical multiplier slices and the fixed-time graph

For a smooth symbol and a smooth compact frequency cutoff, the actual
spacetime multiplier is a Schwartz function. Fubini identifies its spatial
slices with the inverse physical Fourier transform of the published temporal
slice. Fourier inversion then identifies their spatial transforms exactly,
and hence identifies the fixed-time graph in
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The compactly supported frequency datum of the actual multiplier.
Consumer: `cutPhysicalMultiplier`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
def cutMultiplierFrequencyData (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) : SchwartzMap E V :=
  (show HasCompactSupport (fun ξ ↦ (θ ξ * β ξ) • sourceInputFourierTransform v ξ) from
    HasCompactSupport.intro hθcs (fun ξ hξ ↦ by
      simp [image_eq_zero_of_notMem_tsupport hξ])).toSchwartzMap
    ((hθ.mul hβ).smul ((sourceInputFourierTransform v).smooth ⊤))

/-- The actual physical Fourier multiplier, constructed by Fourier inversion
of its compactly supported frequency datum. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
def cutPhysicalMultiplier (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) : SchwartzMap E V :=
  physicalInverseSchwartz (cutMultiplierFrequencyData β θ v hβ hθ hθcs)

/-- The multiplier has precisely the literal physical integral, including
the `(2π)⁻⁽ᵈ⁺¹⁾` normalization and the symbol inside the integral, in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cutPhysicalMultiplier_eq_integral (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (x : E) :
    cutPhysicalMultiplier β θ v hβ hθ hθcs x =
      ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ ξ,
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
          ((θ ξ * β ξ) • sourceInputFourierTransform v ξ) :=
  physicalInverseSchwartz_eq_integral _ x

/-- Fourier inversion verifies that the constructed spacetime function is
the requested multiplier. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_cutPhysicalMultiplier
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (ξ : E) :
    sourceInputFourierTransform (cutPhysicalMultiplier β θ v hβ hθ hθcs) ξ =
      (θ ξ * β ξ) • sourceInputFourierTransform v ξ := by
  rw [cutPhysicalMultiplier, sourceInputFourierTransform_physicalInverseSchwartz]
  rfl

/-- Fubini splits the actual spacetime multiplier into the spatial inverse
transform of the temporal integral. Consumer: `cutPhysicalMultiplierSlice_apply`,
for `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cutPhysicalMultiplier_eq_spatialInverse
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) (y : Euclidean d) :
    cutPhysicalMultiplier β θ v hβ hθ hθcs (timeSpacePoint s y) =
      ((2 * Real.pi) ^ d : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (inner ℝ y η : ℂ)) •
          cutTemporalFourierSlice β θ v s η := by
  rw [cutPhysicalMultiplier_eq_integral]
  simpa only [cutFixedTimeFourierIntegrand, cutFixedTimeFourier, Matrix.one_mulVec,
    inner_eq_time_add_spatial, timeSpacePoint_time, spatialPart_timeSpacePoint,
    Complex.ofReal_add, mul_add, Complex.exp_add, mul_smul] using
    (integral_cutFixedTimeFourier
      (fun _ _ y η ↦ inner ℝ y η) (fun _ _ _ _ ↦ (1 : Matrix (Fin q) (Fin q) ℂ))
      β θ v s s y (by fun_prop) continuous_const hβ.continuous hθ.continuous hθcs)

/-- The fixed-time spatial Schwartz slice, constructed by spatial inversion
of the proved Schwartz temporal slice. `cutPhysicalMultiplierSlice_apply`
identifies it with the actual multiplier, without a slice-identity premise.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutPhysicalMultiplierSlice (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) : SchwartzMap (Euclidean d) V :=
  physicalInverseSchwartz (cutTemporalSchwartz β θ v hβ hθ hθcs s)

/-- The constructed Schwartz slice is pointwise the restriction of the
actual spacetime multiplier. This is the Fourier-inversion/Fubini step in
`app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem cutPhysicalMultiplierSlice_apply
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) (y : Euclidean d) :
    cutPhysicalMultiplierSlice β θ v hβ hθ hθcs s y =
      cutPhysicalMultiplier β θ v hβ hθ hθcs (timeSpacePoint s y) := by
  rw [cutPhysicalMultiplierSlice, physicalInverseSchwartz_eq_integral,
    cutPhysicalMultiplier_eq_spatialInverse]
  rfl

/-- The existing unnormalized physical spatial transform of the actual
multiplier slice is exactly the published temporal Fourier slice. This
discharges the slice identification in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_cutPhysicalMultiplierSlice
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) (η : Euclidean d) :
    sourceInputFourierTransform (cutPhysicalMultiplierSlice β θ v hβ hθ hθcs s) η =
      cutTemporalFourierSlice β θ v s η := by
  rw [cutPhysicalMultiplierSlice, sourceInputFourierTransform_physicalInverseSchwartz,
    cutTemporalSchwartz_apply]

/-- The fixed-time spectral operator is the original spatial graph applied
to the actual multiplier slice. Consumer: the elapsed-graph representation
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cutFixedTimeFourier_eq_graphOperator
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (t s : ℝ) (y : Euclidean d) :
    cutFixedTimeFourier Ψ b β θ v t s y =
      graphOperator (Ψ t s) (fun y _ η ↦ b t s y η)
        (cutPhysicalMultiplierSlice β θ v hβ hθ hθcs s) y := by
  rw [graphOperator_eq_sourceFourierIntegral]
  simp_rw [sourceInputFourierTransform_cutPhysicalMultiplierSlice]
  rfl

/-- The actual elapsed graph is the spatial evolution of the multiplier
slice of the source-masked datum, followed by the output mask. This retains
the order `Mχout U_b Bβ Mχsource` in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cut_elapsedGraph_eq_spatialGraph
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (hΨ : Continuous (Ψ (x 0) (x 0 - r) (spatialPart x)))
    (hb : Continuous (b (x 0) (x 0 - r) (spatialPart x)))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ) :
    graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x =
      χout x • graphOperator (Ψ (x 0) (x 0 - r))
        (fun y _ η ↦ b (x 0) (x 0 - r) y η)
        (cutPhysicalMultiplierSlice β θ
          (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
          hβ hθ hθcs (x 0 - r)) (spatialPart x) := by
  rw [cut_elapsedGraph_eq_fixedTimeFourier Ψ b χout χsource β θ hs r u x
    hΨ hb hβ.continuous hθ.continuous hθcs]
  rw [cutFixedTimeFourier_eq_graphOperator Ψ b β θ _ hβ hθ hθcs]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
