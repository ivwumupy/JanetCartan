module

public import JanetCartan.Analysis.Extension.SeeleyCoefficients.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Limits of Seeley coefficients

Convergence of the products for each fixed node in the proof of
`app:ch_regular_base:lem:ball-extension` of `paper.tex`.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Topology

namespace JanetCartan.Seeley

/-- A factor of the Seeley product, with the omitted diagonal replaced by one. -/
def factor (k j : ℕ) : ℝ :=
  if j = k then 1 else (1 + (2 : ℝ) ^ j) / (2 ^ j - 2 ^ k)

/-- The limiting extension coefficient in
`app:ch_regular_base:eq:extension-infinite-moments`. -/
def coeff (k : ℕ) : ℝ := ∏' j, factor k j

/-- A geometric majorant for the tail of each coefficient product in
`app:ch_regular_base:lem:ball-extension`. -/
theorem factor_tail_bound (k n : ℕ) :
    ‖factor k (n + (k + 1)) - 1‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hy : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ^ (n + (k + 1)) - 2 ^ k =
      2 ^ k * (2 * 2 ^ n - 1) := by rw [pow_add, pow_succ]; ring
  have hpos : 0 < (2 : ℝ) ^ k * (2 * 2 ^ n - 1) := mul_pos (by positivity) (by linarith)
  have heq : factor k (n + (k + 1)) - 1 =
      (1 + (2 : ℝ) ^ k) / (2 ^ k * (2 * 2 ^ n - 1)) := by
    simp only [factor, ite_eq_right (show n + (k + 1) ≠ k by omega)]
    rw [div_sub_one (by rw [hden]; positivity)]
    congr 1
    · ring
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div_pow]
  apply (div_le_iff₀ hpos).2
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hy (show 0 ≤ (2 : ℝ) ^ k by positivity)]

/-- The deviations of the coefficient factors from one form an absolutely summable
series (`app:ch_regular_base:lem:ball-extension`). -/
theorem summable_factor_sub_one (k : ℕ) :
    Summable (fun j ↦ factor k j - 1) := by
  rw [← summable_nat_add_iff (k + 1)]
  exact ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2).of_norm_bounded (factor_tail_bound k)

/-- Each infinite coefficient product converges
(`app:ch_regular_base:lem:ball-extension`). -/
theorem multipliable_factor (k : ℕ) : Multipliable (factor k) := by
  simpa only [add_sub_cancel] using
    Real.multipliable_one_add_of_summable (summable_factor_sub_one k)

/-- The product with a unit diagonal agrees with the manuscript's erased product. -/
theorem finiteCoeff_eq_prod_factor (N k : ℕ) :
    finiteCoeff N k = ∏ j ∈ range (N + 1), factor k j := by
  classical
  rw [finiteCoeff, ← prod_erase (range (N + 1)) (show factor k k = 1 by simp [factor])]
  apply prod_congr rfl
  intro j hj
  simp [factor, (mem_erase.mp hj).1]

/-- The manuscript's finite coefficients converge to `coeff k` for every fixed `k`
(`app:ch_regular_base:lem:ball-extension`). -/
theorem tendsto_finiteCoeff (k : ℕ) :
    Tendsto (fun N ↦ finiteCoeff N k) atTop (𝓝 (coeff k)) := by
  simpa only [finiteCoeff_eq_prod_factor, coeff, Function.comp_def, id_eq] using
    (multipliable_factor k).hasProd.tendsto_prod_nat.comp
      (tendsto_add_atTop_iff_nat 1 |>.2 tendsto_id)

end JanetCartan.Seeley
