module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.KernelIdentity

/-!
# An integrable majorant for source-symbol regularizations

This elementary bound is used only to pass to the exact operator identity in
`app:ch_regular_base:eq:fixed-source-multiplication`. It asserts polynomial
growth, not the separately owned quantitative order-minus-one remainder bound.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- Joint measurability of the literal shift integral used in the operator limit
of `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbol_stronglyMeasurable
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x)) :
    StronglyMeasurable (sourceSymbol S A m x) := by
  exact (by unfold sourceSymbolIntegrand; fun_prop : Continuous
    (fun p : Euclidean n × Euclidean n ↦
      sourceSymbolIntegrand S A m x p.1 p.2)).stronglyMeasurable.integral_prod_right'

/-- A uniform polynomial majorant for the exact source symbol. This is the
majorant needed for the regularized graph limit in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbol_polynomial_majorant
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap (Euclidean n) ℂ) (x η : Euclidean n)
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hbound : ∀ ξ, ‖A x ξ‖ ≤ C * (1 + ‖ξ‖ ^ k)) :
    ‖sourceSymbol S A m x η‖ ≤
      (C * (1 + 2 ^ (k - 1)) *
        ∫ v, ‖sourceFourierTransform m v‖ + ‖v‖ ^ k * ‖sourceFourierTransform m v‖) *
          (1 + ‖η‖ ^ k) := by
  let f := sourceFourierTransform m
  have hi := (f.integrable.norm.add (f.integrable_pow_mul volume k)).const_mul
    (C * (1 + 2 ^ (k - 1)) * (1 + ‖η‖ ^ k))
  have hmajor (v : Euclidean n) :
      ‖sourceSymbolIntegrand S A m x η v‖ ≤
        C * (1 + 2 ^ (k - 1)) * (1 + ‖η‖ ^ k) * (‖f v‖ + ‖v‖ ^ k * ‖f v‖) := by
    have hpow : ‖η + v‖ ^ k ≤ 2 ^ (k - 1) * (‖η‖ ^ k + ‖v‖ ^ k) :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le η v) k).trans
        (add_pow_le (norm_nonneg η) (norm_nonneg v) k)
    have hw : 1 + ‖η + v‖ ^ k ≤
        (1 + 2 ^ (k - 1)) * (1 + ‖η‖ ^ k) * (1 + ‖v‖ ^ k) := by
      have h1 : 0 ≤ ‖η‖ ^ k := by positivity
      have h2 : 0 ≤ ‖v‖ ^ k := by positivity
      have h3 : 0 ≤ (2 : ℝ) ^ (k - 1) := by positivity
      nlinarith [mul_nonneg h1 h2, mul_nonneg h3 (mul_nonneg h1 h2)]
    simp only [sourceSymbolIntegrand, norm_smul, norm_mul,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
    calc
      _ ≤ ‖f v‖ * (C * (1 + ‖η + v‖ ^ k)) :=
        mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
      _ ≤ ‖f v‖ * (C * ((1 + 2 ^ (k - 1)) * (1 + ‖η‖ ^ k) * (1 + ‖v‖ ^ k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hC) (norm_nonneg _)
      _ = _ := by ring
  apply (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hmajor)).trans_eq
  rw [integral_const_mul]
  dsimp only [Pi.add_apply, f]
  ring

end JanetCartan.FourierIntegral
