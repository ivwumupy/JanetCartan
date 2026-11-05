module

public import JanetCartan.Analysis.Operator.Retarded.L2
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Squared L² estimates for derivative expansions

Multiplication and addition estimates for the Leibniz expansions in
`app:ch_osc:prop:osc-retarded-tube`. L² membership is proved alongside each
integral bound, so the estimates do not rely on the value of an undefined integral.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RetardedSobolev

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

/-- Bounded multiplication on L², for the cutoff terms of
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem mul_l2_bound (w f : A → ℂ) (hw : AEStronglyMeasurable w μ)
    (hf : MemLp f 2 μ) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    MemLp (fun x ↦ w x * f x) 2 μ ∧
      (∫ x, ‖w x * f x‖ ^ 2 ∂μ) ≤ C ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hb : ∀ᵐ x ∂μ, ‖w x * f x‖ ≤ C * ‖f x‖ := by
    filter_upwards [hbound] with x hx
    simpa only [norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hm : MemLp (fun x ↦ w x * f x) 2 μ :=
    (hf.norm.const_mul C).mono' (hw.mul hf.aestronglyMeasurable) hb
  refine ⟨hm, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae (hm.integrable_norm_pow (by norm_num))
    ((hf.integrable_norm_pow (by norm_num)).const_mul _)
  filter_upwards [hb] with x hx
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hx

/-- The elementary two-term squared L² bound used for endpoint and cutoff
terms in `app:ch_osc:prop:osc-retarded-tube`. -/
theorem integral_sq_add_le (f g : A → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x + g x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x‖ ^ 2 ∂μ) + 2 * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hfi : Integrable (fun x ↦ ‖f x‖ ^ 2) μ := hf.integrable_norm_pow (by norm_num)
  have hgi : Integrable (fun x ↦ ‖g x‖ ^ 2) μ := hg.integrable_norm_pow (by norm_num)
  calc
    _ ≤ ∫ x, 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 ∂μ := by
      apply integral_mono ((hf.add hg).integrable_norm_pow (by norm_num))
        ((hfi.const_mul 2).add (hgi.const_mul 2))
      intro x
      change ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2
      have ht := (sq_le_sq₀ (norm_nonneg (f x + g x))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (f x) (g x))
      nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
    _ = _ := by rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Squared L² control of a finite Leibniz expansion in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem integral_sq_sum_le {ι : Type*} (s : Finset ι) (f : ι → A → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    (∫ x, ‖∑ i ∈ s, f i x‖ ^ 2 ∂μ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ x, ‖f i x‖ ^ 2 ∂μ := by
  have hi i (h : i ∈ s) := (hf i h).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ x, (s.card : ℝ) * ∑ i ∈ s, ‖f i x‖ ^ 2 ∂μ := by
      apply integral_mono ((memLp_finsetSum s hf).integrable_norm_pow (by norm_num))
        ((integrable_finsetSum s hi).const_mul _)
      intro x
      exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
        (norm_sum_le _ _)).trans sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [integral_const_mul, integral_finsetSum s hi]

end JanetCartan.RetardedSobolev
