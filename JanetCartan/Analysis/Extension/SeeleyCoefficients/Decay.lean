module

public import JanetCartan.Analysis.Extension.SeeleyCoefficients.Limit
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Gaussian bounds for Seeley coefficients

A uniform Gaussian majorant for the construction in
`app:ch_regular_base:eq:extension-coefficient-bound` of `paper.tex`.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Topology

namespace JanetCartan.Seeley

/-- A product form of a Gaussian majorant for the lower-node factors. -/
def decay (k : ℕ) : ℝ := ∏ j ∈ range k, (4 / (2 : ℝ) ^ (j + 1))

/-- The Gaussian majorant is positive at every index. -/
theorem decay_pos (k : ℕ) : 0 < decay k := by
  apply prod_pos
  intro j _
  positivity

/-- The ratio of consecutive values of the Gaussian majorant. -/
theorem decay_succ (k : ℕ) : decay (k + 1) = decay k * (4 / (2 : ℝ) ^ (k + 1)) :=
  prod_range_succ _ _

/-- A lower-node factor contributes a dyadic decay factor
(`app:ch_regular_base:eq:extension-coefficient-bound`). -/
theorem factor_lower_bound {j k : ℕ} (hjk : j < k) :
    ‖factor k j‖ ≤ 4 / (2 : ℝ) ^ (k - j) := by
  have hx : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hy : (2 : ℝ) ≤ 2 ^ (k - j) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ k - j by omega)
  have hpow : (2 : ℝ) ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk.le]
  have hd : (2 : ℝ) ^ j < 2 ^ k :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) hjk
  rw [factor, ite_eq_right hjk.ne, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : 0 < 1 + (2 : ℝ) ^ j), abs_of_neg (sub_neg.mpr hd)]
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left hy (show 0 ≤ (2 : ℝ) ^ j by positivity)]

/-- The factors below the chosen node have a Gaussian product bound. -/
theorem prod_lower_bound (k : ℕ) :
    ‖∏ j ∈ range k, factor k j‖ ≤ decay k := by
  rw [norm_prod, decay, ← prod_range_reflect (fun j ↦ 4 / (2 : ℝ) ^ (j + 1)) k]
  apply prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
  intro j hj
  have hjk := mem_range.mp hj
  convert factor_lower_bound hjk using 1
  congr 2
  omega

/-- The upper-node factors are uniformly bounded, independently of both indices. -/
theorem prod_upper_bound (k m : ℕ) :
    ‖∏ j ∈ range m, factor k (k + 1 + j)‖ ≤ Real.exp 4 := by
  have hfactor (j : ℕ) : ‖factor k (k + 1 + j)‖ ≤ 1 + 2 * (1 / 2 : ℝ) ^ j := by
    have h : ‖factor k (j + (k + 1))‖ ≤ ‖factor k (j + (k + 1)) - 1‖ + 1 := by
      simpa only [sub_add_cancel, norm_one] using
        norm_add_le (factor k (j + (k + 1)) - 1) (1 : ℝ)
    have hb := factor_tail_bound k j
    rw [Nat.add_comm j (k + 1)] at h hb
    linarith
  calc
    _ = ∏ j ∈ range m, ‖factor k (k + 1 + j)‖ := norm_prod _ _
    _ ≤ ∏ j ∈ range m, (1 + 2 * (1 / 2 : ℝ) ^ j) :=
      prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ hfactor j)
    _ ≤ Real.exp (∑ j ∈ range m, 2 * (1 / 2 : ℝ) ^ j) :=
      Real.prod_one_add_le_exp_sum _ (fun _ ↦ by positivity)
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      rw [← mul_sum]
      linarith [sum_geometric_two_le m]

/-- A uniform Gaussian bound for all finite coefficients used in interpolation
(`app:ch_regular_base:eq:extension-coefficient-bound`). -/
theorem finiteCoeff_bound {N k : ℕ} (hk : k ≤ N) :
    ‖finiteCoeff N k‖ ≤ Real.exp 4 * decay k := by
  rw [finiteCoeff_eq_prod_factor]
  have hsplit : N + 1 = (k + 1) + (N - k) := by omega
  rw [hsplit, prod_range_add, prod_range_succ, show factor k k = 1 by simp [factor],
    mul_one, norm_mul]
  calc
    _ ≤ decay k * Real.exp 4 :=
      mul_le_mul (prod_lower_bound k) (prod_upper_bound k (N - k)) (norm_nonneg _)
        (decay_pos k).le
    _ = Real.exp 4 * decay k := mul_comm _ _

/-- The coefficient limits inherit the Gaussian bound
(`app:ch_regular_base:eq:extension-coefficient-bound`). -/
theorem coeff_bound (k : ℕ) : ‖coeff k‖ ≤ Real.exp 4 * decay k := by
  apply le_of_tendsto (tendsto_finiteCoeff k).norm
  filter_upwards [eventually_ge_atTop k] with N hN
  exact finiteCoeff_bound hN

/-- Explicit Gaussian form of the auxiliary majorant. -/
theorem decay_eq (k : ℕ) : decay k = 4 ^ k / (2 : ℝ) ^ (k * (k + 1) / 2) := by
  have hsum : (∑ j ∈ range k, (j + 1)) * 2 = k * (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, add_mul, ih]; ring
  have hexp : (∑ j ∈ range k, (j + 1)) = k * (k + 1) / 2 := by omega
  simp only [decay, prod_div_distrib, prod_const, card_range, prod_pow_eq_pow_sum, hexp]

/-- Gaussian decay of the limiting coefficients. This explicit majorant suffices for
all moments in `app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem coeff_gaussian_bound (k : ℕ) :
    |coeff k| ≤ Real.exp 4 * (4 ^ k / (2 : ℝ) ^ (k * (k + 1) / 2)) := by
  simpa only [Real.norm_eq_abs, decay_eq] using coeff_bound k

/-- The Gaussian majorant remains summable after any dyadic moment weight. -/
theorem summable_decay_moment (ℓ : ℕ) :
    Summable (fun k ↦ decay k * ((2 : ℝ) ^ k) ^ ℓ) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop (ℓ + 2)] with k hk
  have hpow : (2 : ℝ) ^ (ℓ + 3) ≤ 2 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hratio : 4 / (2 : ℝ) ^ (k + 1) * 2 ^ ℓ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [pow_add] at hpow
    norm_num at hpow
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (decay_pos (k + 1)).le (by positivity)),
    Real.norm_of_nonneg (mul_nonneg (decay_pos k).le (by positivity)),
    decay_succ, pow_succ, mul_pow]
  calc
    _ = (4 / (2 : ℝ) ^ (k + 1) * 2 ^ ℓ) * (decay k * (2 ^ k) ^ ℓ) := by ring
    _ ≤ 1 / 2 * (decay k * (2 ^ k) ^ ℓ) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg (decay_pos k).le (by positivity))

end JanetCartan.Seeley
