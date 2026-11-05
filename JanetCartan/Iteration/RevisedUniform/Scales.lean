module

public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses

/-!
# Fixed numerical selectors for the physical revised step

The selectors in this file are independent of the target, scale, finite
history and eventual correction.  They provide one fixed coefficient-profile
reserve and one fixed history derivative order, then choose the initial metric
order before the one-step accuracies.  No wave, inverse, mean or pair field is
introduced here.
-/

@[expose] public noncomputable section

namespace JanetCartan.RevisedUniform

open JanetCartan

/-- One fixed reserve and history order leave the original coefficient-profile
API available while satisfying its `2 + reserve ≤ rStar` side condition.  The
caller supplies every fixed analytic order that the original source/inverse
construction needs; this theorem does not make the baseline-order stub the
final choice. -/
theorem exists_fixed_history_orders_of (n minimumReserve : ℕ) :
    ∃ (reserve rStar kMin : ℕ),
      minimumReserve ≤ reserve ∧
      RevisedScales.baselineOrder n ≤ reserve ∧
      8 ≤ rStar ∧ 2 + reserve ≤ rStar ∧ 1 ≤ kMin ∧
      RevisedScales.displacementLoss n +
          bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) ∧
      RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
        (3 - 2 * growthExponent) * (kMin : ℝ) := by
  let reserve := max minimumReserve (RevisedScales.baselineOrder n)
  let rStar := max 8 (reserve + 2)
  obtain ⟨kMin, hkMin, hcubic, horder⟩ :=
    RevisedScales.exists_initial_order n rStar
  refine ⟨reserve, rStar, kMin, ?_, ?_, ?_, ?_, hkMin, horder, hcubic⟩
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact le_max_left _ _
  · change 2 + reserve ≤ max 8 (reserve + 2)
    simpa only [Nat.add_comm] using Nat.le_max_right 8 (reserve + 2)

/-- Baseline-only convenience specialization.  Final constructions should use
`exists_fixed_history_orders_of` with all source/inverse reserves. -/
theorem exists_fixed_history_orders (n : ℕ) :
    ∃ (reserve rStar kMin : ℕ),
      RevisedScales.baselineOrder n ≤ reserve ∧
      8 ≤ rStar ∧ 2 + reserve ≤ rStar ∧ 1 ≤ kMin ∧
      RevisedScales.displacementLoss n +
          bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) ∧
      RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
        (3 - 2 * growthExponent) * (kMin : ℝ) := by
  obtain ⟨reserve, rStar, kMin, _, hbase, h8, hreserve, hk, horder, hcubic⟩ :=
    exists_fixed_history_orders_of n (RevisedScales.baselineOrder n)
  exact ⟨reserve, rStar, kMin, hbase, h8, hreserve, hk, horder, hcubic⟩

/-- The smoothing-side order inequality follows from the fixed history order.
The left side is deliberately the lower baseline order used by the physical
smoothing producer, while all coefficient and geometry profiles use `rStar`. -/
theorem smoothing_order_of_fixed_history_orders {n reserve rStar kMin : ℕ}
    (hbase : RevisedScales.baselineOrder n ≤ reserve)
    (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    RevisedScales.displacementLoss n +
      bandExponent * (1 + (n : ℝ) / 2) + 2 < (kMin : ℝ) := by
  have hband : 0 ≤ bandExponent := by norm_num [bandExponent]
  have hcast : (1 : ℝ) ≤ (rStar : ℝ) := by
    have : 1 ≤ rStar := by omega
    exact_mod_cast this
  apply lt_of_le_of_lt ?_ horder
  gcongr

/-- Stage orders can be selected uniformly after the correction order is known,
without changing the fixed reserve or any physical object. -/
theorem exists_stage_orders {n reserve k : ℕ} :
    ∃ (m Qp Qm q kCut : ℕ),
      reserve ≤ m ∧ reserve ≤ Qp ∧ reserve ≤ Qm ∧ reserve ≤ q ∧ reserve ≤ kCut ∧
      4 * (k : ℝ) < (1 - coefficientExponent) * (m : ℝ) ∧
      2 * (k : ℝ) + RevisedScales.forcingExponent n +
          (1 + samplingSlack) / 2 < carrierExponent * (Qp : ℝ) ∧
      2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n < (Qm : ℝ) ∧
      2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
        (carrierExponent - separationExponent) * (q : ℝ) ∧
      2 * (k : ℝ) + RevisedScales.cubicLoss n <
        (carrierExponent * cutoffSlack) * (kCut : ℝ) := by
  obtain ⟨m, Qp, Qm, q, kCut, hm, hQp, hQm, hq, hkCut,
      hmQ, hQpQ, hQmQ, hqQ, hkQ⟩ :=
    RevisedScales.exists_step_accuracy_orders n (2 * (k : ℝ)) reserve
  refine ⟨m, Qp, Qm, q, kCut, hm, hQp, hQm, hq, hkCut, ?_, hQpQ,
    hQmQ, hqQ, hkQ⟩
  convert hmQ using 1
  ring

end JanetCartan.RevisedUniform
