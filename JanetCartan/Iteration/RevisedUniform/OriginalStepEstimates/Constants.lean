module

public import JanetCartan.Iteration.RevisedStage.Sobolev

/-!
# The finite common constant in the original physical step

`main:thm:step` uses one coefficient for the separate lower errors and low
norms, then one coefficient for both conclusions. These finite enlargements
cost no frequency power. Their consumer is
`OriginalStepEstimates.increment_estimates_of_source_profiles`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

namespace JanetCartan.RevisedUniform.OriginalStepEstimates

/-- The nine lower source costs, together with the unit normalized mean cost.
All nine entries are fixed before the history by their actual producers. -/
def lowerConstant (cost : Fin 9 → ℝ) : ℝ :=
  1 + ∑ i, |cost i|

/-- The unit mean precision is covered in `main:thm:step`. -/
theorem one_le_lowerConstant (cost : Fin 9 → ℝ) : 1 ≤ lowerConstant cost := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))

/-- The common lower coefficient in `main:thm:step` is nonnegative. -/
theorem lowerConstant_nonneg (cost : Fin 9 → ℝ) : 0 ≤ lowerConstant cost :=
  zero_le_one.trans (one_le_lowerConstant cost)

/-- Every actual lower cost is covered with no scale loss (`main:thm:step`). -/
theorem cost_le_lowerConstant (cost : Fin 9 → ℝ) (i : Fin 9) :
    cost i ≤ lowerConstant cost := by
  have hi : |cost i| ≤ ∑ j, |cost j| :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (cost j)) (Finset.mem_univ i)
  exact (le_abs_self _).trans (hi.trans (le_add_of_nonneg_left zero_le_one))

/-- The final finite maximum uses the literal constants of the physical
Sobolev step, with its fixed embedding coefficient. -/
def finalConstant (n : ℕ) (C CF CH : ℝ) : ℝ :=
  max (2 * RevisedStage.sobolevStageConstant n C)
    (RevisedStage.metricErrorConstant n (2 * RevisedStage.sobolevStageConstant n C)
      CF (PhysicalSobolev.embeddingConstant n * CH))

/-- Nonnegativity of the final physical step coefficient (`main:thm:step`). -/
theorem finalConstant_nonneg {n : ℕ} {C CF CH : ℝ} (hC : 0 ≤ C) :
    0 ≤ finalConstant n C CF CH :=
  (mul_nonneg (by norm_num) (RevisedStage.sobolevStageConstant_bounds hC n).1).trans
    (le_max_left _ _)

/-- The final coefficient covers the physical displacement cost (`main:eq:step-L2`). -/
theorem l2Cost_le_finalConstant (n : ℕ) (C CF CH : ℝ) :
    2 * RevisedStage.sobolevStageConstant n C ≤ finalConstant n C CF CH :=
  le_max_left _ _

/-- The same coefficient covers the full metric cost (`main:eq:step-error`). -/
theorem metricCost_le_finalConstant (n : ℕ) (C CF CH : ℝ) :
    RevisedStage.metricErrorConstant n (2 * RevisedStage.sobolevStageConstant n C)
      CF (PhysicalSobolev.embeddingConstant n * CH) ≤ finalConstant n C CF CH :=
  le_max_right _ _

end JanetCartan.RevisedUniform.OriginalStepEstimates
end
