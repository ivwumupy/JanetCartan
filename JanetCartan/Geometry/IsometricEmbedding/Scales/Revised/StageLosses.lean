module

public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised
public import JanetCartan.Analysis.Iteration.FiniteAccuracy

/-!
# The revised one-step losses and finite accuracy choices

The exact losses in `main:thm:step` of `paper-v2.tex` are used here, without
identifying them with the older `JanetCartan.displacementLoss` or `cubicLoss`.
The consumers are the five component estimates in `new:eq:step-accuracies`
and the prospective increment/error budgets in `new:lem:one-step`.

This module supplies numerical choices only. In particular it does not assert
that the mean, pair, or same-history correction has been constructed.
-/

@[expose] public noncomputable section

namespace JanetCartan.RevisedScales

/-- `main:thm:step`: the revised displacement loss `B₀ = 2A+1+ε+a`. -/
def displacementLoss (n : ℕ) : ℝ :=
  2 * forcingExponent n + 1 + samplingSlack + carrierExponent

/-- `main:thm:step`: the revised cubic loss `B₃ = 2B₀+2am₀`. -/
def cubicLoss (n : ℕ) : ℝ :=
  2 * displacementLoss n + 2 * carrierExponent * baselineOrder n

/-- `main:eq:step-L2`: the revised zero-order loss is positive. -/
theorem displacementLoss_pos (n : ℕ) : 0 < displacementLoss n := by
  unfold displacementLoss forcingExponent samplingSlack carrierExponent
  positivity

/-- `main:eq:Q-choice`: the revised cubic exponent is nonnegative, so the
linear accuracy error is dominated by the same power as the cubic error. -/
theorem cubicLoss_nonneg (n : ℕ) : 0 ≤ cubicLoss n := by
  exact add_nonneg (mul_nonneg (by norm_num) (displacementLoss_pos n).le)
    (mul_nonneg (by norm_num [carrierExponent]) (Nat.cast_nonneg _))

/-- `main:eq:k-cubic` and `main:eq:k-history`: one initial order for the
literal revised losses, chosen before any accuracy, history, or target. -/
theorem exists_initial_order (n rStar : ℕ) :
    ∃ kMin : ℕ, 1 ≤ kMin ∧
      cubicLoss n + 2 * growthExponent + 4 <
        (3 - 2 * growthExponent) * (kMin : ℝ) ∧
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 <
        (kMin : ℝ) :=
  exists_initial_order_for_losses n rStar (displacementLoss n) (cubicLoss n)

/-- `new:eq:step-accuracies`: choose all five finite proof orders at once,
with the same prescribed lower reserve. The orders depend on accuracy but not
on the scale, sample, target, history, or the eventual output derivative order.
The actual five analytic error estimates remain the parent step's obligations. -/
theorem exists_step_accuracy_orders (n : ℕ) (Q : ℝ) (reserve : ℕ) :
    ∃ m Qp Qm q k : ℕ,
      reserve ≤ m ∧ reserve ≤ Qp ∧ reserve ≤ Qm ∧ reserve ≤ q ∧ reserve ≤ k ∧
      2 * Q < (1 - coefficientExponent) * (m : ℝ) ∧
      Q + forcingExponent n + (1 + samplingSlack) / 2 < carrierExponent * (Qp : ℝ) ∧
      Q + 2 * forcingExponent n < (Qm : ℝ) ∧
      Q + 2 * forcingExponent n + 1 + samplingSlack <
        (carrierExponent - separationExponent) * (q : ℝ) ∧
      Q + cubicLoss n < (carrierExponent * cutoffSlack) * (k : ℝ) := by
  obtain ⟨m, hm, hmQ⟩ := exists_nat_order_mul_gt
    (by norm_num [coefficientExponent] : 0 < 1 - coefficientExponent) (2 * Q) reserve
  obtain ⟨Qp, hQp, hQpQ⟩ := exists_nat_order_mul_gt
    (by norm_num [carrierExponent] : 0 < carrierExponent)
    (Q + forcingExponent n + (1 + samplingSlack) / 2) reserve
  obtain ⟨Qm, hQm, hQmQ⟩ := exists_nat_order_mul_gt zero_lt_one
    (Q + 2 * forcingExponent n) reserve
  obtain ⟨q, hq, hqQ⟩ := exists_nat_order_mul_gt
    (by norm_num [carrierExponent, separationExponent] :
      0 < carrierExponent - separationExponent)
    (Q + 2 * forcingExponent n + 1 + samplingSlack) reserve
  obtain ⟨k, hk, hkQ⟩ := exists_nat_order_mul_gt
    (by norm_num [carrierExponent, cutoffSlack] : 0 < carrierExponent * cutoffSlack)
    (Q + cubicLoss n) reserve
  exact ⟨m, Qp, Qm, q, k, hm, hQp, hQm, hq, hk, hmQ, hQpQ,
    by simpa only [one_mul] using hQmQ, hqQ, hkQ⟩

/-- `new:lem:one-step`: absorbing the same step constant into the prospective
L² budget changes no loss and no increment. This is independent of the choice
of physical or periodic norm; the actual norm estimate is supplied by the step. -/
theorem displacement_budget_of_constant_le {n k : ℕ} {C R size : ℝ}
    (hR : 1 ≤ R) (hC : C ≤ R)
    (hsize : size ≤ C * R ^ (-(k : ℝ)) * R ^ displacementLoss n) :
    size ≤ R ^ (-(k : ℝ) + displacementLoss n + 1) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  calc
    size ≤ C * R ^ (-(k : ℝ)) * R ^ displacementLoss n := hsize
    _ ≤ R * R ^ (-(k : ℝ)) * R ^ displacementLoss n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hRp.le _))
        (Real.rpow_nonneg hRp.le _)
    _ = R ^ (1 : ℝ) * R ^ (-(k : ℝ)) * R ^ displacementLoss n := by
      rw [Real.rpow_one]
    _ = R ^ (-(k : ℝ) + displacementLoss n + 1) := by
      rw [← Real.rpow_add hRp, ← Real.rpow_add hRp]
      congr 1
      ring

/-- `main:eq:metric-two-errors`: once `2C ≤ R⁴`, the genuine two-error
estimate at `Q=2k` gives the next metric budget with the revised cubic loss. -/
theorem metric_budget_of_two_errors {n kMin k : ℕ} {C R error : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (habsorb : 2 * C ≤ R ^ (4 : ℕ))
    (horder : cubicLoss n + 2 * growthExponent + 4 <
      (3 - 2 * growthExponent) * (kMin : ℝ)) (hk : kMin ≤ k)
    (herror : error ≤ C * (R ^ (-(k : ℝ)) * R ^ (-2 * (k : ℝ)) +
      (R ^ (-(k : ℝ))) ^ (3 : ℕ) * R ^ cubicLoss n)) :
    error ≤ R ^ (-2 * growthExponent * ((k : ℝ) + 1)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hpower := two_error_powers_le_next (cubicLoss_nonneg n) horder hk hR
  calc
    error ≤ C * (R ^ (-(k : ℝ)) * R ^ (-2 * (k : ℝ)) +
        (R ^ (-(k : ℝ))) ^ (3 : ℕ) * R ^ cubicLoss n) := herror
    _ ≤ C * (2 * (R ^ (-2 * growthExponent * ((k : ℝ) + 1)) * R ^ (-4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpower hC
    _ = (2 * C) * (R ^ (-2 * growthExponent * ((k : ℝ) + 1)) * R ^ (-4 : ℝ)) := by ring
    _ ≤ R ^ (4 : ℕ) * (R ^ (-2 * growthExponent * ((k : ℝ) + 1)) * R ^ (-4 : ℝ)) :=
      mul_le_mul_of_nonneg_right habsorb
        (mul_nonneg (Real.rpow_nonneg hRp.le _) (Real.rpow_nonneg hRp.le _))
    _ = R ^ (-2 * growthExponent * ((k : ℝ) + 1)) := by
      rw [← Real.rpow_natCast R 4, ← mul_assoc, ← Real.rpow_add hRp,
        ← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

end JanetCartan.RevisedScales
