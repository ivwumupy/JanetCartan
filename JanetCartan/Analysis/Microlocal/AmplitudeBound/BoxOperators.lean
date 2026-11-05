module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxScaling

/-!
# Amplitude operator bounds on arbitrary fixed physical boxes

For `app:ch_osc:lem:osc-amplitude`, construct the scalar and normal operator
series directly from a compact Euclidean amplitude. Every coefficient and
modulation bound is discharged here. Identification with the full integral
kernels remains separate; these are bounds for the constructed operator series.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}

/-- Left cutoff modulation on a fixed physical box
(`app:ch_osc:lem:osc-amplitude`). -/
def boxLeftModulation (ℓ : ℝ) (k : Fin (2 * d) → ℤ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  cutoffModulation (leftPositionChart ℓ) (measurable_leftPositionChart ℓ)
    (boxCellCutoff ℓ) (aestronglyMeasurable_boxCellCutoff ℓ)
    (Eventually.of_forall (norm_boxCellCutoff_le ℓ)) k

/-- Right cutoff modulation on a fixed physical box
(`app:ch_osc:lem:osc-amplitude`). -/
def boxRightModulation (ℓ : ℝ) (k : Fin (2 * d) → ℤ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  cutoffModulation (rightPositionChart ℓ) (measurable_rightPositionChart ℓ)
    (boxCellCutoff ℓ) (aestronglyMeasurable_boxCellCutoff ℓ)
    (Eventually.of_forall (norm_boxCellCutoff_le ℓ)) k

/-- The left modulations are contractions (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxLeftModulation_le (ℓ : ℝ) (k : Fin (2 * d) → ℤ) :
    ‖boxLeftModulation ℓ k‖ ≤ 1 := norm_cutoffModulation_le ..

/-- The right modulations are contractions (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxRightModulation_le (ℓ : ℝ) (k : Fin (2 * d) → ℤ) :
    ‖boxRightModulation ℓ k‖ ≤ 1 := norm_cutoffModulation_le ..

/-- The scalar estimate's constant depends only on dimension and box scale
(`app:ch_osc:lem:osc-amplitude`). -/
def boxAmplitudeConstant (d : ℕ) (ℓ : ℝ) : ℝ :=
  coefficientSumConstant d * smoothCoefficientConstant d * boxDerivativeFactor d ℓ

section Symbols

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  (b : X → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hA : 0 ≤ A) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

/-- The actual Fourier coefficient symbols of a compact amplitude on a fixed
box (`app:ch_osc:lem:osc-amplitude`). -/
def boxAmplitudeSymbol (k : Fin (2 * d) → ℤ) : Lp ℂ ∞ μ :=
  periodicAmplitudeSymbol (fun ξ ↦ boxAmplitudePeriodization ℓ (b ξ))
    (stronglyMeasurable_boxAmplitudePeriodization hb ℓ) hd
    (fun ξ ↦ isSmoothPeriodic_boxAmplitudePeriodization hℓ hR (hs ξ) (hf ξ))
    (boxDerivativeFactor d ℓ * A)
    (fun ξ ↦ norm_boxAmplitudePeriodization_le_factor (hzero ξ) ℓ)
    (fun ξ ↦ norm_pureDeriv_boxAmplitudePeriodization_le_factor hℓ hR (hs ξ) (hf ξ) hA (hderiv ξ)) k

/-- The symbols agree with the physical Fourier coefficients almost everywhere
(`app:ch_osc:lem:osc-amplitude`). -/
theorem boxAmplitudeSymbol_coeFn (k : Fin (2 * d) → ℤ) :
    boxAmplitudeSymbol (μ := μ) b hb hd hℓ hR hs hf A hA hzero hderiv k =ᵐ[μ]
      fun ξ ↦ UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (b ξ)) k :=
  periodicAmplitudeSymbol_coeFn ..

/-- Uniform summable coefficient bounds follow from the original physical
amplitude bounds (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxAmplitudeSymbol_le (k : Fin (2 * d) → ℤ) :
    ‖boxAmplitudeSymbol (μ := μ) b hb hd hℓ hR hs hf A hA hzero hderiv k‖ ≤
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) * twoPositionWeight d k :=
  norm_periodicAmplitudeSymbol_le _ _ _ _ _
    (mul_nonneg ((one_le_boxDerivativeFactor d ℓ).trans' zero_le_one) hA) _ _ k

/-- The concrete normal series on a fixed physical box
(`app:ch_osc:eq:two-position-normal-bound`). -/
def boxNormalAmplitudeOperator
    (T : Lp ℂ 2 μ →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (g : Lp ℂ ∞ μ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  normalAmplitudeOperator (boxLeftModulation ℓ) (boxRightModulation ℓ) T
    (fun k ↦ (multiplicationOperator
      (boxAmplitudeSymbol b hb hd hℓ hR hs hf A hA hzero hderiv k)).comp (multiplicationOperator g))

/-- The normal series bound with all coefficient and modulation premises
proved from the compact amplitude (`app:ch_osc:eq:two-position-normal-bound`).
Kernel realization is a separate assertion. -/
theorem norm_boxNormalAmplitudeOperator_le
    (T : Lp ℂ 2 μ →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (g : Lp ℂ ∞ μ) :
    ‖boxNormalAmplitudeOperator b hb hd hℓ hR hs hf A hA hzero hderiv T g‖ ≤
      boxAmplitudeConstant d ℓ * A * ‖T‖ ^ 2 * ‖g‖ := by
  simpa only [boxNormalAmplitudeOperator, boxAmplitudeConstant, mul_assoc] using
    norm_normalAmplitudeOperator_le_of_decay d (boxLeftModulation ℓ) (boxRightModulation ℓ)
      T (boxAmplitudeSymbol b hb hd hℓ hR hs hf A hA hzero hderiv) g
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A))
      (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
      (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A hA hzero hderiv)

end Symbols

section Scalar

variable (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

/-- Scalar operator series for the original amplitude on an arbitrary fixed
box (`app:ch_osc:lem:osc-amplitude`). -/
def boxScalarAmplitudeOperator :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  amplitudeOperator (boxLeftModulation ℓ) (boxRightModulation ℓ)
    (fun k ↦ fourierMultiplier (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv k))

/-- The scalar series satisfies the fixed-box estimate without any assumption
on the frequency support (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxScalarAmplitudeOperator_le :
    ‖boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv‖ ≤
      boxAmplitudeConstant d ℓ * A := by
  simpa only [boxScalarAmplitudeOperator, boxAmplitudeConstant, mul_assoc] using
    norm_amplitudeOperator_fourierMultiplier_le_of_decay d (boxLeftModulation ℓ)
      (boxRightModulation ℓ) (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A))
      (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
      (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)

/-- Finite physical and compact-frequency regularizations on a general fixed
box (`app:ch_osc:lem:osc-amplitude`). -/
def boxRegularizedAmplitudeOperator (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  regularizedAmplitudeOperator (boxLeftModulation ℓ) (boxRightModulation ℓ)
    (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv) s ρ

/-- Uniform regularization bounds on any fixed box
(`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxRegularizedAmplitudeOperator_le (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ) :
    ‖boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv s ρ‖ ≤
      boxAmplitudeConstant d ℓ * A := by
  simpa only [boxRegularizedAmplitudeOperator, boxAmplitudeConstant, mul_assoc] using
    norm_regularizedAmplitudeOperator_le_of_decay d (boxLeftModulation ℓ)
      (boxRightModulation ℓ) (boxAmplitudeSymbol b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A))
      (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
      (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
        ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv) s ρ

/-- The finite fixed-box regularizations converge strongly to the scalar
operator (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxRegularizedAmplitudeOperator
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hsexhaust : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun j ↦ boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv
      (s j) (ρ j) f) m (𝓝 (boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f)) :=
  tendsto_regularizedAmplitudeOperator _ _ _
    (fun k ↦ (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) * twoPositionWeight d k)
    (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
    (norm_boxAmplitudeSymbol_le b hb hd hℓ hR hs hf A
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) hzero hderiv)
    ((summable_twoPositionWeight d).mul_left _) s ρ hsexhaust hρ f

end Scalar

end JanetCartan.AmplitudeBound
