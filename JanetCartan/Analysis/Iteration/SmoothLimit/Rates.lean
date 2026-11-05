module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.Linarith

/-!
# Summable convergence rates

Numerical estimates used after `main:eq:final-Cr` in Section 9.
-/

@[expose] public noncomputable section

open scoped Topology
open Filter

namespace JanetCartan

/-- Section 9 after `main:eq:final-Cr`: inverse superexponential scales are summable,
by comparison with a geometric series using Bernoulli’s inequality. -/
theorem summable_inverse_power_scale {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v) :
    Summable (fun j : ℕ ↦ (R₀ ^ (v ^ j))⁻¹) := by
  have hR : 0 < R₀ := lt_trans zero_lt_one hR₀
  have hq₀ : 0 ≤ R₀ ^ (-(v - 1)) := (Real.rpow_pos_of_pos hR _).le
  have hq₁ : R₀ ^ (-(v - 1)) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hR₀ (by linarith)
  apply Summable.of_nonneg_of_le (fun j ↦ inv_nonneg.mpr (Real.rpow_nonneg hR.le _))
    (fun j ↦ ?_) (summable_geometric_of_lt_one hq₀ hq₁)
  rw [← Real.rpow_neg hR.le, ← Real.rpow_natCast (R₀ ^ (-(v - 1))) j,
    ← Real.rpow_mul hR.le]
  apply Real.rpow_le_rpow_of_exponent_le hR₀.le
  have hj := one_add_mul_sub_le_pow (by linarith : -1 ≤ v) j
  nlinarith

/-- Section 9 after `main:eq:final-Cr`: an order tending to infinity eventually
beats every fixed derivative loss and leaves an inverse-scale bound. -/
theorem eventually_rpow_order_bound {R : ℕ → ℝ} {k : ℕ → ℕ}
    (hR : ∀ j, 1 ≤ R j) (hk : Tendsto k atTop atTop) (b : ℝ) :
    ∀ᶠ j in atTop, (R j) ^ (-(k j : ℝ) + b) ≤ (R j)⁻¹ := by
  have hk' : Tendsto (fun j ↦ (k j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  filter_upwards [hk'.eventually_ge_atTop (b + 1)] with j hj
  rw [← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le (hR j)
  linarith

/-- Section 9 after `main:eq:final-Cr`: any fixed derivative-loss power is summable
once the correction orders tend to infinity and the inverse scales are summable. -/
theorem summable_rpow_order_bound {R : ℕ → ℝ} {k : ℕ → ℕ}
    (hR : ∀ j, 1 ≤ R j) (hRsum : Summable (fun j ↦ (R j)⁻¹))
    (hk : Tendsto k atTop atTop) (b : ℝ) :
    Summable (fun j ↦ (R j) ^ (-(k j : ℝ) + b)) := by
  apply Summable.of_norm_bounded_eventually hRsum
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_rpow_order_bound hR hk b] with j hj
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_nonneg (le_trans zero_le_one (hR j)) _)] using hj

end JanetCartan
