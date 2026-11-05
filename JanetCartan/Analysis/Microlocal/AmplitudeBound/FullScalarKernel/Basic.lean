module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxKernels

/-!
# Full scalar kernels with compact frequency support

Definitions and operator convergence for `app:ch_osc:lem:osc-amplitude`.
The literal kernel retains the original amplitude and uses the unit-period
`2π` Fourier convention. Identifying it with the operator series is separate.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology RealInnerProductSpace

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}

/-- The original compact-frequency oscillatory integral in
`app:ch_osc:lem:osc-amplitude`, with no physical Fourier truncation. -/
def boxScalarAmplitudeKernel
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ρ : ℝ) (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
    Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
      b ξ (pairedPosition x y) * f y

variable (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

/-- The full physical operator series with compact frequency support in
`app:ch_osc:lem:osc-amplitude`. -/
def boxCompactFrequencyAmplitudeOperator (ρ : ℝ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  amplitudeOperator (boxLeftModulation ℓ) (boxRightModulation ℓ)
    (fun k ↦ fourierMultiplier (compactFrequencySymbol ρ
      (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k)))

/-- The compact-frequency series has the same uniform bound as the full
operator (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxCompactFrequencyAmplitudeOperator_le (ρ : ℝ) :
    ‖boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ‖ ≤
      boxAmplitudeConstant d ℓ * A := by
  simpa only [boxCompactFrequencyAmplitudeOperator, boxAmplitudeConstant, mul_assoc] using
    norm_amplitudeOperator_fourierMultiplier_le_of_decay d
      (boxLeftModulation ℓ) (boxRightModulation ℓ)
      (fun k ↦ compactFrequencySymbol ρ (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k))
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A))
      (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
      (fun k ↦ (norm_truncateSymbol_le _ _ _).trans
        (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
          ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k))

/-- Removing just the physical Fourier truncation converges in operator norm
at each fixed frequency radius (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxRegularizedAmplitudeOperator_fixed_frequency (ρ : ℝ) :
    Tendsto (fun s : Finset (Fin (2 * d) → ℤ) ↦
      boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv s ρ) atTop
      (𝓝 (boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ)) := by
  exact hasSum_modulatedTerm (boxLeftModulation ℓ) (boxRightModulation ℓ)
    (fun k ↦ fourierMultiplier (compactFrequencySymbol ρ
      (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k)))
    (fun k ↦ (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) *
      twoPositionWeight d k)
    (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
    (fun k ↦ (norm_fourierMultiplier_le _).trans ((norm_truncateSymbol_le _ _ _).trans
      (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k)))
    ((summable_twoPositionWeight d).mul_left _)

/-- The L² classes of the finite literal kernels converge strongly as the
physical modes are exhausted at fixed radius (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxFiniteAmplitudeKernelLp_fixed_frequency (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun s : Finset (Fin (2 * d) → ℤ) ↦
      boxFiniteAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv s ρ f) atTop
      (𝓝 (boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ f)) := by
  simp_rw [boxFiniteAmplitudeKernelLp_eq]
  exact (ContinuousLinearMap.apply ℂ (Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    f).continuous.continuousAt.tendsto.comp
      (tendsto_boxRegularizedAmplitudeOperator_fixed_frequency
        b hb hd hℓ hR hs hf A hzero hderiv ρ)

/-- Removing compact frequency support in the full physical series converges
strongly on every L² input (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxCompactFrequencyAmplitudeOperator
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦
      boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ f) atTop
      (𝓝 (boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f)) :=
  tendsto_amplitudeOperator_compactFrequencySymbol (boxLeftModulation ℓ)
    (boxRightModulation ℓ) (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
    (fun k ↦ (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) *
      twoPositionWeight d k)
    (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
    (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
    ((summable_twoPositionWeight d).mul_left _) f

end JanetCartan.AmplitudeBound
