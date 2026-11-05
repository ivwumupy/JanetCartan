module

public import JanetCartan.Analysis.Extension.SeeleyCoefficients.Decay

/-!
# The triangular Gaussian rate

The exponent `k * (k + 1) / 2` of
`app:ch_regular_base:eq:extension-coefficient-bound` in `paper.tex`, with an
explicit universal constant `exp 8` obtained from geometric product estimates.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Topology

namespace JanetCartan.Seeley

/-- A refined bound retaining the summable corrections in each lower-node factor. -/
theorem factor_lower_refined {j k : ℕ} (hjk : j < k) :
    ‖factor k j‖ ≤ ((1 + (1 / 2 : ℝ) ^ j) *
      (1 + 2 * (1 / 2 : ℝ) ^ (k - j))) / 2 ^ (k - j) := by
  have hx : (0 : ℝ) < 2 ^ j := by positivity
  have hy : (2 : ℝ) ≤ 2 ^ (k - j) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ k - j by omega)
  have hpow : (2 : ℝ) ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk.le]
  have hd : (2 : ℝ) ^ j < 2 ^ k :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) hjk
  have heq : ‖factor k j‖ = (1 + 1 / (2 : ℝ) ^ j) / (2 ^ (k - j) - 1) := by
    rw [factor, ite_eq_right hjk.ne, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : 0 < 1 + (2 : ℝ) ^ j), abs_of_neg (sub_neg.mpr hd), hpow]
    rw [show -((2 : ℝ) ^ j - 2 ^ j * 2 ^ (k - j)) =
      2 ^ j * (2 ^ (k - j) - 1) by ring]
    field_simp [show (2 : ℝ) ^ (k - j) - 1 ≠ 0 by linarith]
    ring
  rw [heq, one_div_pow, one_div_pow]
  have hrec : 1 / ((2 : ℝ) ^ (k - j) - 1) ≤
      (1 + 2 * (1 / (2 : ℝ) ^ (k - j))) / 2 ^ (k - j) := by
    apply (div_le_div_iff₀ (by linarith) (by positivity)).2
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (k - j))).mp
    field_simp
    nlinarith
  calc
    _ = (1 + 1 / (2 : ℝ) ^ j) * (1 / (2 ^ (k - j) - 1)) := by ring
    _ ≤ (1 + 1 / (2 : ℝ) ^ j) *
        ((1 + 2 * (1 / (2 : ℝ) ^ (k - j))) / 2 ^ (k - j)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by ring

/-- The lower-node product has precisely the triangular Gaussian exponent. -/
theorem prod_lower_gaussian_bound (k : ℕ) :
    ‖∏ j ∈ range k, factor k j‖ ≤ Real.exp 4 / (2 : ℝ) ^ (k * (k + 1) / 2) := by
  have hreflect (f : ℕ → ℝ) :
      (∏ j ∈ range k, f (k - j)) = ∏ j ∈ range k, f (j + 1) := by
    rw [← prod_range_reflect (fun j ↦ f (j + 1)) k]
    apply prod_congr rfl
    intro j hj
    congr 1
    have := mem_range.mp hj
    omega
  have hsum : (∑ j ∈ range k, (j + 1)) * 2 = k * (k + 1) := by
    clear hreflect
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, add_mul, ih]; ring
  have hexp : (∑ j ∈ range k, (j + 1)) = k * (k + 1) / 2 := by omega
  have hfirst : (∏ j ∈ range k, (1 + (1 / 2 : ℝ) ^ j)) ≤ Real.exp 2 :=
    (Real.prod_one_add_le_exp_sum _ (fun _ ↦ by positivity)).trans
      (Real.exp_le_exp.mpr (sum_geometric_two_le k))
  have hsecond : (∏ j ∈ range k, (1 + 2 * (1 / 2 : ℝ) ^ (j + 1))) ≤ Real.exp 2 := by
    simp only [pow_succ]
    have heq (j : ℕ) : 2 * ((1 / 2 : ℝ) ^ j * (1 / 2)) = (1 / 2 : ℝ) ^ j := by ring
    simp_rw [heq]
    exact hfirst
  calc
    _ = ∏ j ∈ range k, ‖factor k j‖ := norm_prod _ _
    _ ≤ ∏ j ∈ range k, ((1 + (1 / 2 : ℝ) ^ j) *
          (1 + 2 * (1 / 2 : ℝ) ^ (k - j))) / 2 ^ (k - j) :=
      prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun _ hj ↦ factor_lower_refined (mem_range.mp hj))
    _ = ((∏ j ∈ range k, (1 + (1 / 2 : ℝ) ^ j)) *
          (∏ j ∈ range k, (1 + 2 * (1 / 2 : ℝ) ^ (j + 1)))) /
          (2 : ℝ) ^ (k * (k + 1) / 2) := by
      rw [prod_div_distrib, prod_mul_distrib,
        hreflect (fun j ↦ 1 + 2 * (1 / 2 : ℝ) ^ j),
        hreflect (fun j ↦ (2 : ℝ) ^ j), prod_pow_eq_pow_sum, hexp]
    _ ≤ (Real.exp 2 * Real.exp 2) / (2 : ℝ) ^ (k * (k + 1) / 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hfirst hsecond (prod_nonneg (fun _ _ ↦ by positivity))
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; norm_num

/-- Uniform finite-coefficient decay at the rate of
`app:ch_regular_base:eq:extension-coefficient-bound`. -/
theorem finiteCoeff_gaussian_bound {N k : ℕ} (hk : k ≤ N) :
    ‖finiteCoeff N k‖ ≤ Real.exp 8 / (2 : ℝ) ^ (k * (k + 1) / 2) := by
  rw [finiteCoeff_eq_prod_factor]
  have hsplit : N + 1 = (k + 1) + (N - k) := by omega
  rw [hsplit, prod_range_add, prod_range_succ, show factor k k = 1 by simp [factor],
    mul_one, norm_mul]
  calc
    _ ≤ (Real.exp 4 / (2 : ℝ) ^ (k * (k + 1) / 2)) * Real.exp 4 :=
      mul_le_mul (prod_lower_gaussian_bound k) (prod_upper_bound k (N - k))
        (norm_nonneg _) (by positivity)
    _ = Real.exp 8 / (2 : ℝ) ^ (k * (k + 1) / 2) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]; norm_num

/-- Limiting-coefficient decay with exactly the triangular exponent of
`app:ch_regular_base:eq:extension-coefficient-bound`. -/
theorem coeff_triangular_bound (k : ℕ) :
    |coeff k| ≤ Real.exp 8 / (2 : ℝ) ^ (k * (k + 1) / 2) := by
  apply le_of_tendsto (tendsto_finiteCoeff k).abs
  filter_upwards [eventually_ge_atTop k] with N hN
  exact finiteCoeff_gaussian_bound hN

end JanetCartan.Seeley
