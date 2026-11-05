module

public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.FiniteMoment

/-!
# Scalar absorption in the revised physical metric step

The consumers are §15, `main:eq:primary-strain`, `new:eq:uncut-error`, and the
cutoff paragraph proving `main:eq:step-error` in `paper-v2.tex`. The losses are
the existing literal `RevisedScales.displacementLoss` and `RevisedScales.cubicLoss`.
All assertions are scalar deductions from the displayed LOWER component bounds;
none asserts construction of the waves, mean response, pair response, or cutoff.
The five strict integer budgets are already supplied by
`RevisedScales.exists_step_accuracy_orders` and are not redefined here.
-/

@[expose] public noncomputable section

namespace JanetCartan.RevisedStage

/-- The exact revised cubic loss is twice the loss of each C¹ factor in
`new:eq:uncut-error`, with the integer `m₀ = floor(n/2)+2`. -/
theorem cubicLoss_eq_twice_derivative_loss (n : ℕ) :
    RevisedScales.cubicLoss n =
      2 * (RevisedScales.displacementLoss n +
        carrierExponent * RevisedScales.baselineOrder n) := by
  unfold RevisedScales.cubicLoss
  ring

/-- The common C¹ exponent in §15 Step 5 is nonnegative. -/
theorem derivative_loss_nonneg (n : ℕ) :
    0 ≤ RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n :=
  add_nonneg (RevisedScales.displacementLoss_pos n).le
    (mul_nonneg (by norm_num [carrierExponent]) (Nat.cast_nonneg _))

/-- `main:eq:smoothing-combined`: reuse the two-tail theorem for the SAME
finite-moment tensor, at the coefficient scale `T₀ = Rᵗ`. The common constant
is retained, rather than assuming the desired accuracy tail. -/
theorem smoothing_error_le_of_accuracy {E C δ R Q : ℝ} {m : ℕ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (hm : 2 * Q < (1 - coefficientExponent) * (m : ℝ))
    (hsmall : E ≤ C * δ ^ 2)
    (hhigh : E ≤ C * (R ^ coefficientExponent / R) ^ m) :
    E ≤ C * δ * R ^ (-Q) := by
  have h := DefectSmoothing.finiteMoment_two_tail_bound hE hC hC hδ hR
    (Real.rpow_nonneg (zero_lt_one.trans_le hR).le _) le_rfl hm.le hsmall hhigh
  simpa only [← pow_two, Real.sqrt_sq hC] using h

/-- `main:eq:primary-strain`: the exact wave accuracy absorbs the square-root
sample count and the REVISED forcing factor, preserving one factor of `δ`. -/
theorem primary_error_le_of_accuracy {n Qp : ℕ} {E C δ R Q : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (hQp : Q + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (Qp : ℝ))
    (hE : E ≤ C * δ * R ^ (RevisedScales.forcingExponent n +
      (1 + samplingSlack) / 2 - carrierExponent * (Qp : ℝ))) :
    E ≤ C * δ * R ^ (-Q) := by
  exact hE.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (mul_nonneg hC hδ))

/-- The elementary amplitude absorption in §15 Step 3: `δ² ≤ δ`. -/
theorem quadratic_amplitude_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 ≤ δ := by
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]

/-- `main:eq:mean-equation`: the normalized mean error, after multiplication
by the ACTUAL `b² = δ² R^(2A)`, is absorbed at precisely `Qm > Q+2A`. -/
theorem mean_error_le_of_accuracy {n Qm : ℕ} {E C δ R Q : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hQm : Q + 2 * RevisedScales.forcingExponent n < (Qm : ℝ))
    (hE : E ≤ C * R ^ (-(Qm : ℝ))) :
    (δ * R ^ RevisedScales.forcingExponent n) ^ 2 * E ≤
      C * δ * R ^ (-Q) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hp : (R ^ RevisedScales.forcingExponent n) ^ 2 =
      R ^ (2 * RevisedScales.forcingExponent n) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  calc
    _ ≤ (δ * R ^ RevisedScales.forcingExponent n) ^ 2 *
        (C * R ^ (-(Qm : ℝ))) := mul_le_mul_of_nonneg_left hE (sq_nonneg _)
    _ = C * δ ^ 2 * R ^ (2 * RevisedScales.forcingExponent n - (Qm : ℝ)) := by
      rw [mul_pow, hp, Real.rpow_sub hRp, Real.rpow_neg hRp.le]
      ring
    _ ≤ C * δ * R ^ (-Q) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (quadratic_amplitude_le hδ hδ1) hC
      · exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      · positivity
      · positivity

/-- `main:prop:pairs` in §15 Step 3: retain the precise `R^(1+ε)` count and
`(λh)^(-q)` gain, with the revised forcing exponent; no weaker loss is used. -/
theorem pair_error_le_of_accuracy {n q : ℕ} {E C δ R Q : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hq : Q + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (q : ℝ))
    (hE : E ≤ C * δ ^ 2 * R ^ (2 * RevisedScales.forcingExponent n +
      1 + samplingSlack - (carrierExponent - separationExponent) * (q : ℝ))) :
    E ≤ C * δ * R ^ (-Q) := by
  apply hE.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (quadratic_amplitude_le hδ hδ1) hC
  · exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  · exact Real.rpow_nonneg (zero_lt_one.trans_le hR).le _
  · exact mul_nonneg hC hδ

/-- §15 Step 6: the actual tail profile `δ R^B₀ λ^(m₀-ζk)` supplies the
stronger derivative tail needed to absorb the SAME background's C¹ growth.
The sole accuracy condition is the exact `aζk > Q+B₃`. -/
theorem cutoff_derivative_le_of_accuracy {n k : ℕ} {E C δ R Q : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (hk : Q + RevisedScales.cubicLoss n < carrierExponent * cutoffSlack * (k : ℝ))
    (hE : E ≤ C * δ * R ^ RevisedScales.displacementLoss n *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
        cutoffSlack * (k : ℝ))) :
    E ≤ C * δ * R ^ (-Q - (RevisedScales.displacementLoss n +
      carrierExponent * RevisedScales.baselineOrder n)) := by
  have hb : RevisedScales.displacementLoss n +
      carrierExponent * (RevisedScales.baselineOrder n : ℝ) +
      (Q + (RevisedScales.displacementLoss n +
        carrierExponent * RevisedScales.baselineOrder n)) ≤
      (carrierExponent * cutoffSlack) * (k : ℝ) := by
    rw [cubicLoss_eq_twice_derivative_loss] at hk
    linarith
  have h := rpow_cutoff_tail_le hR hb
  calc
    _ ≤ (C * δ) * (R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) -
          cutoffSlack * (k : ℝ))) := by simpa only [mul_assoc] using hE
    _ ≤ (C * δ) * R ^ (-(Q + (RevisedScales.displacementLoss n +
        carrierExponent * RevisedScales.baselineOrder n))) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg hC hδ)
    _ = _ := by congr 2; ring

end JanetCartan.RevisedStage
