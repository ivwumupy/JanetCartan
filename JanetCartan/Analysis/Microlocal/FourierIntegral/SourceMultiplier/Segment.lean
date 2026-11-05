module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exact source FTC formula

The argument is the segment in the paragraph following
`app:ch_regular_base:eq:fixed-source-multiplication`. Smoothness is required of
the supplied extensions, including the angular and bounded-frequency pieces.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral

variable {n r : ℕ}

attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Direct differentiation of the manuscript's segment. Both amplitude and phase
contributions are retained (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem hasDerivAt_sourceSymbolSegment
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η v : Euclidean n) (t : ℝ)
    (hS : DifferentiableAt ℝ (S x) (η + t • v))
    (hA : DifferentiableAt ℝ (A x) (η + t • v)) :
    HasDerivAt (sourceSymbolSegment S A x η v)
      (sourceSymbolSegmentDerivative S A x η v t) t := by
  have hline : HasDerivAt (fun t : ℝ ↦ η + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add η
  have hphase := ((hS.hasFDerivAt.comp_hasDerivAt t hline).sub_const (S x η)).add
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const
      (inner ℝ (gradient (S x) η) v))
  have hexp := (hphase.ofReal_comp.const_mul Complex.I).cexp
  have hprod := hexp.smul (hA.hasFDerivAt.comp_hasDerivAt t hline)
  unfold sourceSymbolSegment
  simpa [sourceSymbolSegmentDerivative, inner_add_left, inner_neg_left,
    inner_gradient_left, smul_add, smul_smul, sub_eq_add_neg] using! hprod

/-- Continuity of the explicit differentiated segment follows from `C¹` phase
and amplitude extensions (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem continuous_sourceSymbolSegmentDerivative
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η v : Euclidean n) (hS : ContDiff ℝ 1 (S x)) (hA : ContDiff ℝ 1 (A x)) :
    Continuous (sourceSymbolSegmentDerivative S A x η v) := by
  have hS' := hS.continuous_fderiv (by simp)
  have hA' := hA.continuous_fderiv (by simp)
  unfold sourceSymbolSegmentDerivative
  simp only [inner_sub_left, inner_gradient_left]
  fun_prop

/-- The exact FTC endpoint difference, with no small-shift restriction, for the
extended phase and amplitude of `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem integral_sourceSymbolSegmentDerivative
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η v : Euclidean n) (hS : ContDiff ℝ 1 (S x)) (hA : ContDiff ℝ 1 (A x)) :
    (∫ t in (0 : ℝ)..1, sourceSymbolSegmentDerivative S A x η v t) =
      Complex.exp (Complex.I * ((S x (η + v) - S x η : ℝ) : ℂ)) • A x (η + v) -
      Complex.exp (Complex.I * (inner ℝ (gradient (S x) η) v : ℂ)) • A x η := by
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_sourceSymbolSegment S A x η v t
      ((hS.differentiable (by simp)).differentiableAt)
      ((hA.differentiable (by simp)).differentiableAt))
    ((continuous_sourceSymbolSegmentDerivative S A x η v hS hA).intervalIntegrable 0 1)
  simpa [sourceSymbolSegment] using hd

/-- The exact remainder is the integral of the two FTC contributions in
`app:ch_regular_base:eq:fixed-source-multiplication`. The polynomial symbol bound
is the only growth input. In particular Fourier inversion and convergence of the
shift integral are conclusions of preceding proofs, not additional hypotheses. -/
theorem sourceRemainder_eq_integral_segmentDerivative
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (hS : ContDiff ℝ 1 (S x)) (hA : ContDiff ℝ 1 (A x)) (C : ℝ) (k : ℕ)
    (hbound : ∀ v, ‖A x (η + v)‖ ≤ C * (1 + ‖v‖ ^ k)) :
    sourceRemainder S A m x η =
      ∫ v, sourceFourierTransform m v •
        ∫ t in (0 : ℝ)..1, sourceSymbolSegmentDerivative S A x η v t := by
  have hi := sourceSymbolIntegrand_integrable S A m x η hS.continuous hA.continuous C k hbound
  have hp : Integrable (fun v ↦ (sourceFourierTransform m v *
      Complex.exp (Complex.I * (inner ℝ (gradient (S x) η) v : ℂ))) • A x η) := by
    apply ((sourceFourierTransform m).integrable.norm.mul_const ‖A x η‖).mono'
    · exact (by fun_prop : Continuous (fun v ↦ (sourceFourierTransform m v *
        Complex.exp (Complex.I * (inner ℝ (gradient (S x) η) v : ℂ))) •
          A x η)).aestronglyMeasurable
    · filter_upwards [] with v
      simp only [norm_smul, norm_mul]
      rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp_rw [integral_sourceSymbolSegmentDerivative S A x η _ hS hA,
    smul_sub, smul_smul]
  change Integrable (fun v ↦ (sourceFourierTransform m v *
    Complex.exp (Complex.I * ((S x (η + v) - S x η : ℝ) : ℂ))) • A x (η + v)) at hi
  rw [integral_sub hi hp, integral_smul_const]
  simp_rw [mul_comm (sourceFourierTransform m _), sourceFourierTransform_inversion]
  simp only [sourceRemainder, sourceSymbol, sourceSymbolIntegrand, mul_comm]

/-- The principal term plus the exact FTC remainder in
`app:ch_regular_base:eq:fixed-source-multiplication`, deduced from `C¹` extensions
and their ordinary polynomial amplitude bound. This is a symbol identity; the
operator identity with the input Fourier cutoff is proved separately by
`graphOperator_sourceSymbol_inputCutoff`. -/
theorem sourceSymbol_eq_principal_add_integral
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (hS : ContDiff ℝ 1 (S x)) (hA : ContDiff ℝ 1 (A x)) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ ξ, ‖A x ξ‖ ≤ C * (1 + ‖ξ‖ ^ k)) :
    sourceSymbol S A m x η = m (gradient (S x) η) • A x η +
      ∫ v, sourceFourierTransform m v •
        ∫ t in (0 : ℝ)..1, sourceSymbolSegmentDerivative S A x η v t := by
  obtain ⟨D, hD⟩ := sourceAmplitude_shifted_growth A x η C hC k hbound
  have hr := sourceRemainder_eq_integral_segmentDerivative S A m x η hS hA D k hD
  rw [sourceRemainder, sub_eq_iff_eq_add] at hr
  simpa only [add_comm] using hr

end JanetCartan.FourierIntegral
