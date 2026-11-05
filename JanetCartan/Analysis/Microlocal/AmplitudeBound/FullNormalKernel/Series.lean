module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxKernels
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Summation tools for the full normal kernel

The series/integral interchange and almost-everywhere summation steps of
`app:ch_osc:eq:two-position-normal-bound` in `paper.tex`. The integrable weight
in the interchange lemma is an explicit intermediate premise; compact-kernel
integrability and identification of the Hilbert adjoint are separate steps.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.AmplitudeBound

/-- An integrable weight permits termwise integration of a uniformly absolutely
convergent amplitude expansion (`app:ch_osc:eq:two-position-normal-bound`). -/
theorem hasSum_integral_mul_of_summable_bound
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ι → X → ℂ} {b q : X → ℂ} {w : ι → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hbound : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ w k) (hw : Summable w)
    (hq : Integrable q μ) (hs : ∀ᵐ x ∂μ, HasSum (fun k ↦ F k x) (b x)) :
    HasSum (fun k ↦ ∫ x, F k x * q x ∂μ) (∫ x, b x * q x ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun k x ↦ w k * ‖q x‖)
  · exact fun k ↦ (hF k).mul hq.aestronglyMeasurable
  · intro k
    filter_upwards [hbound k] with x hx
    simpa only [norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (q x))
  · exact Eventually.of_forall fun x ↦ hw.mul_right ‖q x‖
  · simpa only [tsum_mul_right] using hq.norm.const_mul (∑' k, w k)
  · exact hs.mono fun x hx ↦ hx.mul_right (q x)

/-- The absolutely convergent operator series also converges pointwise almost
everywhere on every L² input (`app:ch_osc:lem:osc-amplitude`). -/
theorem amplitudeOperator_hasSum_ae
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    (L R C : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w : ι → ℝ)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (hC : ∀ k, ‖C k‖ ≤ w k) (hw : Summable w) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, HasSum (fun k ↦ L k (C k (R k f)) x)
      (amplitudeOperator L R C f x) := by
  have hn : Summable (fun k ↦ ‖L k (C k (R k f))‖) := by
    apply (hw.mul_right ‖f‖).of_norm_bounded
    intro k
    simpa only [norm_norm, modulatedTerm, ContinuousLinearMap.comp_apply] using ((modulatedTerm L R C k).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_modulatedTerm_le L R C w hL hR hC k)
        (norm_nonneg f))
  rw [amplitudeOperator_apply L R C w hL hR hC hw]
  apply Lp.hasSum_coeFn_tsum
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hn)

section PhysicalExpansion

variable {d : ℕ}

/-- One literal cutoff Fourier term of the physical amplitude in
`app:ch_osc:eq:two-position-normal-bound`. -/
def boxAmplitudeFourierTerm (b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ℓ : ℝ) (k : Fin (2 * d) → ℤ) (x y : EuclideanSpace ℝ (Fin d)) : ℂ :=
  (boxCellCutoff ℓ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
    UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ b) k *
    (boxCellCutoff ℓ y * UnitAddTorus.mFourier k (rightPositionChart ℓ y))

/-- Strong measurability of the cutoff, including for measures other than
volume, used in `app:ch_osc:eq:two-position-normal-bound`. -/
theorem stronglyMeasurable_boxCellCutoff (ℓ : ℝ) :
    StronglyMeasurable (boxCellCutoff (d := d) ℓ) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin d) ↦ ℓ⁻¹ • x) := by fun_prop
  exact ((stronglyMeasurable_const (b := (1 : ℂ))).indicator
    (isCompact_fundamentalCell d).measurableSet).comp_measurable hm

/-- Uniform summable bounds for the literal Fourier terms, before taking
L∞ equivalence classes (`app:ch_osc:eq:two-position-normal-bound`). -/
theorem norm_boxAmplitudeFourierTerm_le (hd : 0 < d)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R b)
    (hf : ContDiff ℝ ∞ b) {A : ℝ} (hzero : ∀ z, ‖b z‖ ≤ A)
    (hderiv : ∀ i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) b z‖ ≤ A)
    (k : Fin (2 * d) → ℤ) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖boxAmplitudeFourierTerm b ℓ k x y‖ ≤
      (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) * twoPositionWeight d k := by
  have hchar (p : EuclideanSpace ℝ (Fin d) → Torus (2 * d)) (z) :
      ‖boxCellCutoff ℓ z * UnitAddTorus.mFourier k (p z)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_boxCellCutoff_le ℓ z)
      (norm_mFourier_apply_le_one k (p z)) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hc := norm_mFourierCoeff_le_twoPositionWeight hd
    (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR hs hf)
    (norm_boxAmplitudePeriodization_le_factor hzero ℓ)
    (norm_pureDeriv_boxAmplitudePeriodization_le_factor hℓ hR hs hf
      ((norm_nonneg (b 0)).trans (hzero 0)) hderiv) k
  calc
    ‖boxAmplitudeFourierTerm b ℓ k x y‖ ≤
        ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ b) k‖ := by
      dsimp only [boxAmplitudeFourierTerm]
      rw [norm_mul, norm_mul]
      calc
        _ ≤ 1 * ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ b) k‖ * 1 := by
          gcongr
          · exact hchar _ x
          · exact hchar _ y
        _ = _ := by ring
    _ ≤ _ := hc

/-- Joint measurability survives Fourier expansion and evaluation along
measurable positions (`app:ch_osc:eq:two-position-normal-bound`). -/
theorem stronglyMeasurable_boxAmplitudeFourierTerm
    {X : Type*} [MeasurableSpace X]
    (b : X → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (ℓ : ℝ)
    (k : Fin (2 * d) → ℤ) {x y : X → EuclideanSpace ℝ (Fin d)}
    (hx : Measurable x) (hy : Measurable y) :
    StronglyMeasurable (fun a ↦ boxAmplitudeFourierTerm (b a) ℓ k (x a) (y a)) := by
  have hl := (UnitAddTorus.mFourier k).continuous.stronglyMeasurable.comp_measurable
    ((measurable_leftPositionChart ℓ).comp hx)
  have hr := (UnitAddTorus.mFourier k).continuous.stronglyMeasurable.comp_measurable
    ((measurable_rightPositionChart ℓ).comp hy)
  exact (((stronglyMeasurable_boxCellCutoff ℓ).comp_measurable hx).mul hl).mul
    (stronglyMeasurable_parameter_mFourierCoeff _
      (stronglyMeasurable_boxAmplitudePeriodization hb ℓ) k) |>.mul
        (((stronglyMeasurable_boxCellCutoff ℓ).comp_measurable hy).mul hr)

/-- Exact termwise integration of the physical Fourier expansion against an
integrable weight. The compact-kernel argument supplies that weight for
`app:ch_osc:eq:two-position-normal-bound`. -/
theorem hasSum_integral_boxAmplitude_expansion
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (b : X → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : ∀ a, SupportedInCenteredBox R (b a)) (hf : ∀ a, ContDiff ℝ ∞ (b a))
    {A : ℝ} (hzero : ∀ a z, ‖b a z‖ ≤ A)
    (hderiv : ∀ a i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b a) z‖ ≤ A)
    {x y : X → EuclideanSpace ℝ (Fin d)} (hx : Measurable x) (hy : Measurable y)
    {q : X → ℂ} (hq : Integrable q μ) :
    HasSum (fun k ↦ ∫ a, boxAmplitudeFourierTerm (b a) ℓ k (x a) (y a) * q a ∂μ)
      (∫ a, b a (pairedPosition (x a) (y a)) * q a ∂μ) := by
  apply hasSum_integral_mul_of_summable_bound
    (fun k ↦ (stronglyMeasurable_boxAmplitudeFourierTerm b hb ℓ k hx hy).aestronglyMeasurable)
    (fun k ↦ Eventually.of_forall fun a ↦ norm_boxAmplitudeFourierTerm_le hd hℓ hR
      (hs a) (hf a) (hzero a) (hderiv a) k (x a) (y a))
    ((summable_twoPositionWeight d).mul_left _) hq
  exact Eventually.of_forall fun a ↦
    hasSum_boxAmplitude_expansion hd hℓ hR (hs a) (hf a) (hzero a) (hderiv a) (x a) (y a)

end PhysicalExpansion

section NormalOperator

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}

/-- Almost-everywhere summation of the actual normal coefficient operators,
with every coefficient bound discharged from the physical hypotheses of
`app:ch_osc:eq:two-position-normal-bound`. -/
theorem boxNormalAmplitudeOperator_hasSum_ae
    (c : X → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hc : StronglyMeasurable (Function.uncurry c)) (hd : 0 < d)
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : ∀ u, SupportedInCenteredBox R (c u)) (hf : ∀ u, ContDiff ℝ ∞ (c u))
    (A : ℝ) (hA : 0 ≤ A) (hzero : ∀ u z, ‖c u z‖ ≤ A)
    (hderiv : ∀ u i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (c u) z‖ ≤ A)
    (T : Lp ℂ 2 μ →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (g : Lp ℂ ∞ μ) (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ∀ᵐ x, HasSum (fun k ↦ boxLeftModulation ℓ k
      (T (multiplicationOperator (boxAmplitudeSymbol c hc hd hℓ hR hs hf A hA hzero hderiv k)
        (multiplicationOperator g (T.adjoint (boxRightModulation ℓ k f))))) x)
      (boxNormalAmplitudeOperator c hc hd hℓ hR hs hf A hA hzero hderiv T g f x) := by
  let a := boxAmplitudeSymbol (μ := μ) c hc hd hℓ hR hs hf A hA hzero hderiv
  let C := fun k ↦ (multiplicationOperator (a k)).comp (multiplicationOperator g)
  let w := fun k ↦ (smoothCoefficientConstant d * (boxDerivativeFactor d ℓ * A)) *
    twoPositionWeight d k
  have ha (k) : ‖a k‖ ≤ w k :=
    norm_boxAmplitudeSymbol_le c hc hd hℓ hR hs hf A hA hzero hderiv k
  have hC (k) : ‖C k‖ ≤ w k * ‖g‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul ((norm_multiplicationOperator_le _).trans (ha k))
        (norm_multiplicationOperator_le _) (norm_nonneg _) ((norm_nonneg _).trans (ha k)))
  exact amplitudeOperator_hasSum_ae (boxLeftModulation ℓ) (boxRightModulation ℓ)
    (normalCoefficient T C) (fun k ↦ w k * ‖T‖ ^ 2 * ‖g‖)
    (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
    (norm_normalCoefficient_le T C w ‖g‖ hC)
    ((((summable_twoPositionWeight d).mul_left _).mul_right _).mul_right _) f

end NormalOperator

end JanetCartan.AmplitudeBound
