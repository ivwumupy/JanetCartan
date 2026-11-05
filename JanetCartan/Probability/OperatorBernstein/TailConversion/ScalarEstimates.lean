module

public import JanetCartan.Probability.OperatorBernstein.ScalarOptimization
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Scalar exponential estimates for the Bernstein tail

Minsker (3.7)–(3.8), used in `app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

namespace JanetCartan.OperatorBernstein

/-- Strict positivity of the exponential remainder at positive arguments
(`app:ch_waves:thm:sampling`, Minsker (3.2)). -/
theorem expRemainder_pos {x : ℝ} (hx : 0 < x) : 0 < expRemainder x := by
  have := Real.add_one_lt_exp hx.ne'
  unfold expRemainder
  linarith

/-- Monotonicity on the positive half-line, used for spectral event inclusion in
`app:ch_waves:thm:sampling`. -/
theorem expRemainder_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    expRemainder x ≤ expRemainder y := by
  have h₁ := Real.add_one_le_exp (y - x)
  have h₂ : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have h₃ := mul_le_mul_of_nonneg_left h₁ (Real.exp_pos x).le
  rw [← Real.exp_add] at h₃
  have he : x + (y - x) = y := by ring
  rw [he] at h₃
  unfold expRemainder
  nlinarith

/-- The cubic Taylor lower bound used in Minsker (3.8)
(`app:ch_waves:thm:sampling`). -/
theorem quadratic_cubic_le_expRemainder {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 2 + x ^ 3 / 6 ≤ expRemainder x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  unfold expRemainder
  linarith

/-- Minsker (3.8), the exponential-to-remainder ratio
(`app:ch_waves:thm:sampling`). -/
theorem exp_div_expRemainder_le {x : ℝ} (hx : 0 < x) :
    Real.exp x / expRemainder x ≤ 1 + 6 / x ^ 2 := by
  have hp := expRemainder_pos hx
  have hlow := quadratic_cubic_le_expRemainder hx.le
  have hsq : 0 < x ^ 2 := sq_pos_of_pos hx
  apply (div_le_iff₀ hp).2
  apply (mul_le_mul_iff_right₀ hsq).mp
  have he : x ^ 2 * ((1 + 6 / x ^ 2) * expRemainder x) =
      (x ^ 2 + 6) * expRemainder x := by field_simp
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ 6 by norm_num)
  unfold expRemainder at *
  nlinarith

private theorem factorial_add_two_lower (n : ℕ) :
    2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ, pow_succ]
    nlinarith

/-- Minsker (3.7), bounding the exponential remainder by a geometric series
(`app:ch_waves:thm:sampling`). -/
theorem expRemainder_le_geometric {x : ℝ} (hx : 0 ≤ x) (hx3 : x < 3) :
    expRemainder x ≤ x ^ 2 / (2 * (1 - x / 3)) := by
  have hs : HasSum (fun n : ℕ ↦ x ^ (n + 2) / (n + 2).factorial)
      (expRemainder x) := by
    rw [hasSum_nat_add_iff (f := fun n : ℕ ↦ x ^ n / n.factorial) 2]
    convert NormedSpace.expSeries_div_hasSum_exp x using 1
    rw [← Real.exp_eq_exp_ℝ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add]
    unfold expRemainder
    ring
  have hg := (hasSum_geometric_of_lt_one (show 0 ≤ x / 3 by positivity)
    (show x / 3 < 1 by linarith)).mul_left (x ^ 2 / 2)
  have hc : ∀ n : ℕ, x ^ (n + 2) / (n + 2).factorial ≤ x ^ 2 / 2 * (x / 3) ^ n := by
    intro n
    calc
      _ ≤ x ^ (n + 2) / (2 * 3 ^ n) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast factorial_add_two_lower n
      _ = _ := by
        rw [pow_add, div_pow]
        field_simp
  have h := hs.summable.tsum_le_tsum hc hg.summable
  rw [hs.tsum_eq, hg.tsum_eq] at h
  simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using h

/-- The scaled version of Minsker (3.7) for `app:ch_waves:thm:sampling`. -/
theorem expRemainder_div_sq_le {θ R : ℝ} (hθ : 0 ≤ θ) (hR : 0 < R)
    (hθR : θ * R < 3) :
    expRemainder (θ * R) / R ^ 2 ≤ θ ^ 2 / (2 * (1 - θ * R / 3)) := by
  have h := div_le_div_of_nonneg_right
    (expRemainder_le_geometric (mul_nonneg hθ hR.le) hθR) (sq_nonneg R)
  convert h using 1
  field_simp

/-- Substituting the Bernstein parameter into the two-sided trace ratio gives
exactly the constant fourteen in `app:ch_waves:thm:sampling` (Minsker (3.9)). -/
theorem two_trace_ratio_le_tailBound {R v τ t : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hτ : 0 ≤ τ) (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    2 * (τ / v * Real.exp (expRemainder (bernsteinParameter R v t * R) / R ^ 2 * v)) /
        expRemainder (bernsteinParameter R v t * t) ≤ tailBound R v τ t := by
  let θ := bernsteinParameter R v t
  have hθ : 0 < θ := bernsteinParameter_pos hR.le hv ht
  have hθR : θ * R < 3 := bernsteinParameter_mul_lt_three hR.le hv ht.le
  have hx : 0 < θ * t := mul_pos hθ ht
  have hφ := expRemainder_pos hx
  have hτv : 0 ≤ τ / v := div_nonneg hτ hv.le
  have hrem := expRemainder_div_sq_le hθ.le hR hθR
  have hratio := exp_div_expRemainder_le hx
  have hpref : 1 + 6 / (θ * t) ^ 2 ≤ 7 :=
    bernsteinParameter_prefactor_le_seven hR.le hv ht.le hthreshold
  have hexp : θ ^ 2 / (2 * (1 - θ * R / 3)) * v - θ * t =
      -(t ^ 2) / (2 * (v + R * t / 3)) := by
    simpa only [div_mul_eq_mul_div] using bernsteinParameter_exponent hR.le hv ht.le
  change 2 * (τ / v * Real.exp (expRemainder (θ * R) / R ^ 2 * v)) /
    expRemainder (θ * t) ≤ _
  calc
    _ = 2 * (τ / v) * Real.exp (expRemainder (θ * R) / R ^ 2 * v - θ * t) *
        (Real.exp (θ * t) / expRemainder (θ * t)) := by
      rw [Real.exp_sub]
      field_simp
    _ ≤ 2 * (τ / v) * Real.exp (θ ^ 2 / (2 * (1 - θ * R / 3)) * v - θ * t) *
        (1 + 6 / (θ * t) ^ 2) := by
      gcongr
    _ ≤ 2 * (τ / v) * Real.exp (θ ^ 2 / (2 * (1 - θ * R / 3)) * v - θ * t) * 7 := by
      exact mul_le_mul_of_nonneg_left hpref (by positivity)
    _ = tailBound R v τ t := by rw [hexp, tailBound]; ring

end JanetCartan.OperatorBernstein
