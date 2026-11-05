module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Scalar exponential remainder bound

The scalar power-series estimate underlying Appendix A and (3.3) of Minsker,
used in `app:ch_waves:thm:sampling`.
-/

@[expose] public noncomputable section

namespace JanetCartan.OperatorBernstein

/-- The exponential remainder is its power series starting at degree two
(Minsker Appendix A; `app:ch_waves:thm:sampling`). -/
theorem expRemainder_eq_tsum (x : ℝ) :
    expRemainder x = ∑' n : ℕ, x ^ (n + 2) / (n + 2).factorial := by
  have h := (NormedSpace.expSeries_div_summable x).sum_add_tsum_nat_add 2
  have he : Real.exp x = ∑' n : ℕ, x ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [← he] at h
  unfold expRemainder
  linarith

/-- Scalar quadratic upper bound for the exponential on `[-R,R]`, including
negative scalar arguments (Minsker Appendix A; `app:ch_waves:thm:sampling`). -/
theorem exp_le_quadratic_of_abs_le {x R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ)
    (hx : |x| ≤ R) :
    Real.exp (θ * x) ≤ 1 + θ * x + (expRemainder (θ * R) / R ^ 2) * x ^ 2 := by
  have hs (y : ℝ) : Summable (fun n : ℕ => y ^ (n + 2) / (n + 2).factorial) :=
    (summable_nat_add_iff 2).mpr (NormedSpace.expSeries_div_summable y)
  have hp (n : ℕ) : (θ * x) ^ (n + 2) ≤ (x ^ 2 / R ^ 2) * (θ * R) ^ (n + 2) := by
    have hn : x ^ n ≤ R ^ n :=
      (le_abs_self (x ^ n)).trans (by simpa only [abs_pow] using (pow_le_pow_left₀ (abs_nonneg x) hx n))
    calc
      (θ * x) ^ (n + 2) = (θ ^ (n + 2) * x ^ 2) * x ^ n := by
        rw [mul_pow, pow_add x]; ring
      _ ≤ (θ ^ (n + 2) * x ^ 2) * R ^ n :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (pow_nonneg hθ _) (sq_nonneg x))
      _ = (x ^ 2 / R ^ 2) * (θ * R) ^ (n + 2) := by
        rw [mul_pow, pow_add R]
        field_simp
  have h := (hs (θ * x)).tsum_le_tsum
    (fun n => show (θ * x) ^ (n + 2) / (n + 2).factorial ≤
      (x ^ 2 / R ^ 2) * ((θ * R) ^ (n + 2) / (n + 2).factorial) from by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hp n) (by positivity))
    ((hs (θ * R)).mul_left (x ^ 2 / R ^ 2))
  rw [tsum_mul_left, ← expRemainder_eq_tsum, ← expRemainder_eq_tsum] at h
  unfold expRemainder at *
  have heq : x ^ 2 / R ^ 2 * (Real.exp (θ * R) - θ * R - 1) =
      (Real.exp (θ * R) - θ * R - 1) / R ^ 2 * x ^ 2 := by ring
  rw [heq] at h
  linarith

end JanetCartan.OperatorBernstein
