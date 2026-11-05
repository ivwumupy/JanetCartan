module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Literal source-multiplication kernel

For a frequency-integrable amplitude (in particular a compact frequency
regularization), the shift integral has an integrable frequency majorant.
Fubini and physical Fourier inversion give the exact kernel identity in
`app:ch_regular_base:eq:fixed-source-multiplication`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Absolute joint convergence of the shifted symbol for an integrable amplitude.
This is the Fubini input for the literal regularizations of
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolIntegrand_integrable_prod
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (hAi : Integrable (A x)) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      sourceSymbolIntegrand S A m x p.2 p.1) (volume.prod volume) := by
  have hm := ((sourceFourierTransform m).integrable (μ := volume)).norm.mul_prod hAi.norm
  have ht := ((measurePreserving_prod_add_right (volume : Measure (Euclidean n)) volume).integrable_comp hm.aestronglyMeasurable).mpr hm
  apply ht.mono'
  · exact (by unfold sourceSymbolIntegrand; fun_prop : Continuous
      (fun p : Euclidean n × Euclidean n ↦ sourceSymbolIntegrand S A m x p.2 p.1)).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [sourceSymbolIntegrand, norm_smul, norm_mul, Function.comp_apply]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The regularized source symbol is integrable in its remaining covector, as
required by the operator Fubini step in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbol_integrable_of_integrable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (hAi : Integrable (A x)) :
    Integrable (sourceSymbol S A m x) :=
  (sourceSymbolIntegrand_integrable_prod S A m x hS hA hAi).swap.integral_prod_left

/-- Pointwise phase bookkeeping for the source shift in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOscillation_smul_sourceSymbolIntegrand
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x y η v : Euclidean n) :
    graphOscillation S x y η • sourceSymbolIntegrand S A m x η v =
      (Complex.exp (Complex.I * (inner ℝ y v : ℂ)) * sourceFourierTransform m v) •
        (graphOscillation S x y (η + v) • A x (η + v)) := by
  simp only [sourceSymbolIntegrand, graphOscillation, smul_smul]
  congr 1
  rw [mul_left_comm _ (sourceFourierTransform m v), ← mul_assoc,
    mul_comm _ (sourceFourierTransform m v), mul_assoc, ← Complex.exp_add,
    mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [inner_add_right, Complex.ofReal_sub, Complex.ofReal_add]
  ring

/-- Actual Fourier inversion and Fubini prove the matrix kernel identity for
integrable amplitudes, including every compact frequency regularization.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem integral_graphOscillation_sourceSymbol
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x y : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) (hAi : Integrable (A x)) :
    (∫ η, graphOscillation S x y η • sourceSymbol S A m x η) =
      m y • ∫ η, graphOscillation S x y η • A x η := by
  have hi : Integrable (fun p : Euclidean n × Euclidean n ↦
      graphOscillation S x y p.1 • sourceSymbolIntegrand S A m x p.1 p.2)
      (volume.prod volume) := by
    apply (sourceSymbolIntegrand_integrable_prod S A m x hS hA hAi).swap.norm.mono'
    · exact (by unfold graphOscillation sourceSymbolIntegrand; fun_prop : Continuous
        (fun p : Euclidean n × Euclidean n ↦ graphOscillation S x y p.1 •
          sourceSymbolIntegrand S A m x p.1 p.2)).aestronglyMeasurable
    · filter_upwards [] with p
      simp only [norm_smul, graphOscillation, mul_comm Complex.I,
        Complex.norm_exp_ofReal_mul_I, one_mul, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, le_refl]
  simp only [sourceSymbol, ← integral_smul]
  rw [integral_integral_swap hi]
  simp_rw [graphOscillation_smul_sourceSymbolIntegrand, integral_smul]
  simp_rw [integral_add_right_eq_self
    (fun η ↦ graphOscillation S x y η • A x η)]
  rw [integral_smul_const, sourceFourierTransform_inversion]

end JanetCartan.FourierIntegral
