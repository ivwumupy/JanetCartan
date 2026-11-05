module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Orders
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedBackgroundProfiles
public meta import Lean

/-!
# Fixed numerical and differentiability inputs for the actual step

Private proof terms used by the original-data application of
`main:thm:step`. The current map is the actual selected reference plus the
given Schwartz prefix. The five orders are the single existing joint choice.
The finite maximum is reached at the current scale, separately from the
initial `Tpair` gate. No analytic source estimate is assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
open scoped ContDiff
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

private theorem current_differentiable (d : ℕ) (hn : 5 ≤ d + 1) (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean (d + 1)) (Euclidean (embeddingDimension (d + 1))))
    (x : Euclidean (d + 1)) :
    DifferentiableAt ℝ (RevisedGlobal.finiteMap (OriginalSelectedPrehistory.Gmap d hn) u) x := by
  have h : ContDiff ℝ ∞ (RevisedGlobal.finiteMap (OriginalSelectedPrehistory.Gmap d hn) u) :=
    (OriginalSelectedPrehistory.Gref d hn).contDiff.add
      (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  exact h.differentiable (by simp) x

private theorem accuracy_budgets (n k : ℕ) :
    0 ≤ 2 * (k : ℝ) ∧
    2 * (2 * (k : ℝ)) <
      (1 - coefficientExponent) * (OriginalUniformCorrection.smoothingOrder n k : ℝ) ∧
    2 * (k : ℝ) + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (OriginalUniformCorrection.primaryOrder n k : ℝ) ∧
    2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n <
      (OriginalUniformCorrection.meanOrder n k : ℝ) ∧
    2 * (k : ℝ) + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (OriginalUniformCorrection.pairOrder n k : ℝ) ∧
    2 * (k : ℝ) + RevisedScales.cubicLoss n <
      carrierExponent * cutoffSlack * (OriginalUniformCorrection.cutoffOrder n k : ℝ) := by
  obtain ⟨_, _, _, _, _, hm, hp, hv, hs, hc⟩ := OriginalUniformCorrection.orders_spec n k
  exact ⟨by positivity, by nlinarith, hp, hv, hs, hc⟩

private def stageMaximum (preparation smoothing tensor precision frame : ℝ) : ℝ :=
  max 2 (max preparation (max smoothing (max tensor (max precision frame))))

private theorem stageMaximum_two_le (preparation smoothing tensor precision frame : ℝ) :
    2 ≤ stageMaximum preparation smoothing tensor precision frame := le_max_left _ _

private theorem stageMaximum_reaches (preparation smoothing tensor precision frame R : ℝ)
    (h : stageMaximum preparation smoothing tensor precision frame ≤ R) :
    preparation ≤ R ∧ smoothing ≤ R ∧ tensor ≤ R ∧ precision ≤ R ∧ frame ≤ R := by
  have hrest : max preparation (max smoothing (max tensor (max precision frame))) ≤ R :=
    (le_max_right _ _).trans h
  have htail : max smoothing (max tensor (max precision frame)) ≤ R :=
    (le_max_right _ _).trans hrest
  have htwo : max tensor (max precision frame) ≤ R := (le_max_right _ _).trans htail
  have hlast : max precision frame ≤ R := (le_max_right _ _).trans htwo
  exact ⟨(le_max_left _ _).trans hrest, (le_max_left _ _).trans htail,
    (le_max_left _ _).trans htwo, (le_max_left _ _).trans hlast, (le_max_right _ _).trans hlast⟩

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
open Lean Meta

/-- The exact five current-stage frequency inputs; its caller supplies only
the original static producers (`main:thm:step`). -/
def stageThreshold (frequencies : Array Expr) : MetaM Expr := do
  unless frequencies.size == 5 do throwError "actual step threshold: five original current gates required"
  pure (mkAppN (mkConst ``stageMaximum) frequencies)

/-- Reach the original five stage gates with no initial-threshold substitution. -/
def stageThresholdReaches (frequencies : Array Expr) (R h : Expr) : MetaM Expr := do
  unless frequencies.size == 5 do throwError "actual step threshold: changed frequency tuple"
  pure (mkAppN (mkConst ``stageMaximum_reaches) (frequencies ++ #[R,h]))

/-- Positivity of the original step's current-stage maximum. -/
def stageThresholdTwoLe (frequencies : Array Expr) : MetaM Expr := do
  unless frequencies.size == 5 do throwError "actual step threshold: changed frequency tuple"
  pure (mkAppN (mkConst ``stageMaximum_two_le) frequencies)

/-- All five accuracy budgets at `Q=2k`, using the same joint order selector. -/
def actualAccuracyProofs (n k : Expr) : Expr :=
  mkAppN (mkConst ``accuracy_budgets) #[n,k]

/-- Actual global differentiability of the original physical history. -/
def actualCurrentDifferentiable (d hn j u : Expr) : Expr :=
  mkAppN (mkConst ``current_differentiable) #[d,hn,j,u]

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
