module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PeriodicSymbols
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PositionCharts

/-!
# The concrete two-position operator series

Construct the operator series of `app:ch_osc:lem:osc-amplitude` from a smooth
periodic amplitude and physical cutoffs. All coefficient estimates and modulation
bounds are proved from the stated data. The amplitude parameter is unit-period
frequency; the physical frequency is `2π ξ`. The finite regularizations have
bounds independent of both cutoffs and converge strongly and distributionally.

The subsequent `PhysicalKernel` module identifies finite regularizations with
literal oscillatory integrals; `CompactAmplitude` connects the construction to
compact Euclidean amplitudes in a normalized box.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}
  (b : EuclideanSpace ℝ (Fin d) → Torus (2 * d) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ)
  (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)
  (ℓ : ℝ) (χ ψ : EuclideanSpace ℝ (Fin d) → ℂ)
  (hχ : AEStronglyMeasurable χ) (hψ : AEStronglyMeasurable ψ)
  (hχbound : ∀ᵐ x, ‖χ x‖ ≤ 1) (hψbound : ∀ᵐ y, ‖ψ y‖ ≤ 1)

/-- The concrete cutoff-modulated Fourier series in `app:ch_osc:lem:osc-amplitude`. -/
def physicalAmplitudeOperator :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  amplitudeOperator
    (cutoffModulation (leftPositionChart ℓ) (measurable_leftPositionChart ℓ) χ hχ hχbound)
    (cutoffModulation (rightPositionChart ℓ) (measurable_rightPositionChart ℓ) ψ hψ hψbound)
    (fun k ↦ fourierMultiplier (periodicAmplitudeSymbol b hb hd hf A hzero hderiv k))

/-- The concrete finite physical/compact frequency regularization in
`app:ch_osc:lem:osc-amplitude`. -/
def regularizedPhysicalAmplitudeOperator (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  regularizedAmplitudeOperator
    (cutoffModulation (leftPositionChart ℓ) (measurable_leftPositionChart ℓ) χ hχ hχbound)
    (cutoffModulation (rightPositionChart ℓ) (measurable_rightPositionChart ℓ) ψ hψ hψbound)
    (periodicAmplitudeSymbol b hb hd hf A hzero hderiv) s ρ

/-- The scalar two-position series bound in `app:ch_osc:lem:osc-amplitude` from
physical derivative bounds, without a frequency-support assumption. -/
theorem norm_physicalAmplitudeOperator_le :
    ‖physicalAmplitudeOperator b hb hd hf A hzero hderiv ℓ χ ψ hχ hψ hχbound hψbound‖ ≤
      (coefficientSumConstant d * smoothCoefficientConstant d) * A := by
  simpa only [physicalAmplitudeOperator, mul_assoc] using norm_amplitudeOperator_fourierMultiplier_le_of_decay d _ _
    (periodicAmplitudeSymbol b hb hd hf A hzero hderiv) (smoothCoefficientConstant d * A)
    (fun k ↦ norm_cutoffModulation_le (leftPositionChart ℓ)
      (measurable_leftPositionChart ℓ) χ hχ hχbound k)
    (fun k ↦ norm_cutoffModulation_le (rightPositionChart ℓ)
      (measurable_rightPositionChart ℓ) ψ hψ hψbound k)
    (norm_periodicAmplitudeSymbol_le b hb hd hf A ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)

/-- The scalar regularization bound in `app:ch_osc:lem:osc-amplitude` is uniform
in the finite physical sum and compact frequency radius. -/
theorem norm_regularizedPhysicalAmplitudeOperator_le
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ) :
    ‖regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv ℓ χ ψ
      hχ hψ hχbound hψbound s ρ‖ ≤
      (coefficientSumConstant d * smoothCoefficientConstant d) * A := by
  simpa only [regularizedPhysicalAmplitudeOperator, mul_assoc] using norm_regularizedAmplitudeOperator_le_of_decay d _ _
    (periodicAmplitudeSymbol b hb hd hf A hzero hderiv) (smoothCoefficientConstant d * A)
    (fun k ↦ norm_cutoffModulation_le (leftPositionChart ℓ)
      (measurable_leftPositionChart ℓ) χ hχ hχbound k)
    (fun k ↦ norm_cutoffModulation_le (rightPositionChart ℓ)
      (measurable_rightPositionChart ℓ) ψ hψ hψbound k)
    (norm_periodicAmplitudeSymbol_le b hb hd hf A ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv) s ρ

/-- Strong convergence of the concrete finite regularizations in
`app:ch_osc:lem:osc-amplitude`. Only exhaustion of the two cutoffs is assumed. -/
theorem tendsto_regularizedPhysicalAmplitudeOperator
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hs : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun j ↦ regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv
      ℓ χ ψ hχ hψ hχbound hψbound (s j) (ρ j) f) m
      (𝓝 (physicalAmplitudeOperator b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound f)) :=
  tendsto_regularizedAmplitudeOperator _ _ _
    (fun k ↦ (smoothCoefficientConstant d * A) * twoPositionWeight d k)
    (fun k ↦ norm_cutoffModulation_le (leftPositionChart ℓ)
      (measurable_leftPositionChart ℓ) χ hχ hχbound k)
    (fun k ↦ norm_cutoffModulation_le (rightPositionChart ℓ)
      (measurable_rightPositionChart ℓ) ψ hψ hψbound k)
    (norm_periodicAmplitudeSymbol_le b hb hd hf A ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
    ((summable_twoPositionWeight d).mul_left _) s ρ hs hρ f

/-- The concrete regularizations converge as tempered distributions in
`app:ch_osc:lem:osc-amplitude`. Their identification with regularized integral
kernels remains separate. -/
theorem tendsto_regularizedPhysicalAmplitudeOperator_temperedDistribution
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hs : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun j ↦ Lp.toTemperedDistribution
      (regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound (s j) (ρ j) f)) m
      (𝓝 (Lp.toTemperedDistribution (physicalAmplitudeOperator b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound f))) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).continuous.continuousAt.tendsto.comp
      (tendsto_regularizedPhysicalAmplitudeOperator b hb hd hf A hzero hderiv
        ℓ χ ψ hχ hψ hχbound hψbound s ρ hs hρ f)

end JanetCartan.AmplitudeBound
