module

public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingPreparation

/-!
# The same five finite orders for the original uniform correction

The consumer is `UniformHistoryCorrection.correction` at `Q = 2k` in
`paper-v2.tex`, `new:eq:step-accuracies`.  Retain the moment order already used
by `OriginalMetricPreparation.original_smoothing_plan`, and take the other
four orders from that very existential witness.  None of these choices changes
the reference, history reserve, source cutoff, sample, or initial threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

namespace JanetCartan.RevisedUniform.OriginalUniformCorrection

/-- The actual smoothing plan's order with its positive minimum reserve. -/
def smoothingOrder (n k : ℕ) : ℕ :=
  PhysicalMean.OriginalCompleteForcing.stepMomentOrder n k 0

/-- The primary accuracy from the same joint choice as `smoothingOrder`. -/
def primaryOrder (n k : ℕ) : ℕ :=
  (exists_stage_orders (n := n) (k := k) (reserve := max 1 0)).choose_spec.choose

/-- The mean accuracy from the same joint choice as `smoothingOrder`. -/
def meanOrder (n k : ℕ) : ℕ :=
  (exists_stage_orders (n := n) (k := k) (reserve := max 1 0)).choose_spec.choose_spec.choose

/-- The signed-product accuracy from the same joint choice as `smoothingOrder`. -/
def pairOrder (n k : ℕ) : ℕ :=
  (exists_stage_orders (n := n) (k := k) (reserve := max 1 0)).choose_spec.choose_spec.choose_spec.choose

/-- The Fourier-tail order from the same joint choice as `smoothingOrder`. -/
def cutoffOrder (n k : ℕ) : ℕ :=
  (exists_stage_orders (n := n) (k := k) (reserve := max 1 0)).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- All five literal v2 inequalities, before the history and target dilation.
The first order is definitionally the previously selected smoothing order. -/
theorem orders_spec (n k : ℕ) :
    1 ≤ smoothingOrder n k ∧
    1 ≤ primaryOrder n k ∧
    1 ≤ meanOrder n k ∧
    1 ≤ pairOrder n k ∧
    1 ≤ cutoffOrder n k ∧
    4 * (k : ℝ) < (1 - coefficientExponent) * (smoothingOrder n k : ℝ) ∧
    2 * (k : ℝ) + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (primaryOrder n k : ℝ) ∧
    2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n < (meanOrder n k : ℝ) ∧
    2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (pairOrder n k : ℝ) ∧
    2 * (k : ℝ) + RevisedScales.cubicLoss n <
      (carrierExponent * cutoffSlack) * (cutoffOrder n k : ℝ) := by
  exact (exists_stage_orders (n := n) (k := k) (reserve := max 1 0)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end JanetCartan.RevisedUniform.OriginalUniformCorrection
end
