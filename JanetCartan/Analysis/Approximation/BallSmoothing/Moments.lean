module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Finite binomial moments for smoothing on a ball

The coefficients in `paper-v2.tex`,
`app:ch_regular_base:eq:extension-finite-moments`, cancel precisely the
positive Taylor orders below `m` in the inward radial formula
`app:ch_regular_base:eq:extension-radial-formula`. The proof applies the
actual finite-difference identity to a monomial. The absolute coefficient
sum also supplies a constant for the smoothing estimates.
-/

@[expose] public noncomputable section

open Finset

namespace JanetCartan.BallSmoothing

/-- The literal finite binomial coefficient in
`app:ch_regular_base:eq:extension-finite-moments`; the radial formula uses
only `1 ≤ j ≤ m`. -/
def coefficient (m j : ℕ) : ℝ := (-1) ^ (j - 1) * (m.choose j : ℝ)

private theorem range_eq_insert_Icc (m : ℕ) :
    range (m + 1) = insert 0 (Icc 1 m) := by
  ext j
  simp only [mem_range, mem_insert, mem_Icc]
  omega

private theorem alternating_binomial_moment_zero {m k : ℕ} (hk : k < m) :
    ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) * (j : ℝ) ^ k = 0 := by
  have hdiff := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hk) 0
  rw [fwdDiff_iter_eq_sum_shift] at hdiff
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, nsmul_eq_mul, mul_one, zero_add, Pi.zero_apply] at hdiff
  have hsum := congrArg (fun t : ℝ ↦ (-1 : ℝ) ^ m * t) hdiff
  rw [mul_zero, mul_sum] at hsum
  convert hsum using 1
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
  have hsign : (-1 : ℝ) ^ m * (-1) ^ (m - j) = (-1) ^ j := by
    rw [← pow_add, show m + (m - j) = 2 * (m - j) + j by omega,
      pow_add, pow_mul]
    norm_num
  rw [← mul_assoc, ← mul_assoc, hsign]

private theorem coefficient_eq_neg (m j : ℕ) (hj : 1 ≤ j) :
    coefficient m j = -((-1 : ℝ) ^ j * (m.choose j : ℝ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
  simp [coefficient, pow_succ]

/-- The exact finite moment identity of
`app:ch_regular_base:eq:extension-finite-moments`: the zeroth moment is one
and all positive moments below `m` vanish. -/
theorem sum_coefficient_mul_pow {m k : ℕ} (hm : 1 ≤ m) (hk : k < m) :
    ∑ j ∈ Icc 1 m, coefficient m j * (j : ℝ) ^ k = if k = 0 then 1 else 0 := by
  have hzero := alternating_binomial_moment_zero hk
  rw [range_eq_insert_Icc, sum_insert (by simp)] at hzero
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero] at hzero
  have hsum : (∑ j ∈ Icc 1 m, coefficient m j * (j : ℝ) ^ k) =
      -(∑ j ∈ Icc 1 m, (-1 : ℝ) ^ j * (m.choose j : ℝ) * (j : ℝ) ^ k) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    rw [coefficient_eq_neg m j (mem_Icc.mp hj).1, neg_mul]
  rw [hsum]
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hpower : (0 : ℝ) ^ k = if k = 0 then 1 else 0 := by
    by_cases hk0 : k = 0 <;> simp [hk0]
  rw [← hpower]
  linarith

/-- The radial smoothing formula preserves its constant Taylor term
(`app:ch_regular_base:eq:extension-finite-moments`). -/
theorem sum_coefficient {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ Icc 1 m, coefficient m j = 1 := by
  simpa using sum_coefficient_mul_pow hm (show 0 < m from hm)

/-- Positive Taylor terms below `m` cancel in the inward radial formula
(`app:ch_regular_base:eq:extension-finite-moments`). -/
theorem sum_coefficient_mul_pow_eq_zero {m k : ℕ} (hm : 1 ≤ m)
    (hk0 : 1 ≤ k) (hk : k < m) :
    ∑ j ∈ Icc 1 m, coefficient m j * (j : ℝ) ^ k = 0 := by
  simpa only [ite_eq_right (Nat.ne_zero_of_lt hk0)] using sum_coefficient_mul_pow hm hk

/-- The sign in each finite smoothing coefficient has absolute value one
(`app:ch_regular_base:eq:extension-finite-moments`). -/
@[simp] theorem abs_coefficient (m j : ℕ) :
    |coefficient m j| = (m.choose j : ℝ) := by
  simp [coefficient, abs_mul]

/-- The exact absolute coefficient sum in the finite radial formula is
`2^m - 1`; this is a constant depending only on the approximation order
in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem sum_abs_coefficient (m : ℕ) :
    ∑ j ∈ Icc 1 m, |coefficient m j| = (2 : ℝ) ^ m - 1 := by
  have htotal : (∑ j ∈ range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [range_eq_insert_Icc, sum_insert (by simp)] at htotal
  simp only [Nat.choose_zero_right, Nat.cast_one] at htotal
  simp only [abs_coefficient]
  linarith

end JanetCartan.BallSmoothing
