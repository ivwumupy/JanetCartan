module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ThresholdsTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
import all JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
import all JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The actual original-data current-stage threshold

One `T(k)` reaches the actual preparation, smoothing, normalized tensor,
requested mean precision and frame budgets at the current scale. Its only
inputs are the original metric/domain and the accuracy. The reference and
signed-size threshold remain the fixed `Tpair` at the initial scale.
Consumer: `step_of_primary_strain` and then the actual uniform correction
(`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepThresholdsTemplate

open Lean Meta Elab Command
open OriginalStepEstimatesTemplate

private def root := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def save (key : Name) (params : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual step threshold: history or unresolved data entered {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "actual step threshold: unavailable producer metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Checking actual step threshold {key}/{params.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original-data current-stage frequency maximum, fixed on the original metric/domain and accuracy before every initial scale, history and target dilation. It reaches exactly preparation, same-smoother, normalized tensor, requested precision and frame budgets; initial Tpair is unchanged (main:thm:step; main:prop:current-scale)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual step threshold: nonstandard axioms {axioms}"
  logInfo m!"PASS actual original step threshold {key}/{params.size}: {axioms}"

run_meta do
  let fixedType ← getConstInfo `JanetCartan.RevisedUniform.OriginalMetricPreparation.metricCap
  forallBoundedTelescope fixedType.type (some 7) fun fixed result => do
    unless fixed.size == 7 && result.isConstOf ``Real do
      throwError "actual step threshold: original metric7 changed"
    withLocalDeclD `k (mkConst ``Nat) fun k => do
      let frequencies ← originalStageFrequencies fixed fixed[:2].toArray k
      save `T (fixed.push k) (← stageThreshold frequencies) (mkConst ``Real) true

run_meta do
  forallBoundedTelescope (← getConstInfo (root ++ `T)).type (some 8) fun p _ => do
    let frequencies ← originalStageFrequencies p[:7].toArray p[:2].toArray p[7]!
    let proof ← stageThresholdTwoLe frequencies
    let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 2,app (root ++ `T) p]
    save `T_ge_two p proof target

run_meta do
  forallBoundedTelescope (← getConstInfo (root ++ `T)).type (some 8) fun p _ => do
    let frequencies ← originalStageFrequencies p[:7].toArray p[:2].toArray p[7]!
    withLocalDeclD `R (mkConst ``Real) fun R => do
      let gate ← mkAppM ``LE.le #[app (root ++ `T) p,R]
      withLocalDeclD `hT gate fun hT => do
        let proof ← stageThresholdReaches frequencies R hT
        save `T_reaches (p ++ #[R,hT]) proof (← inferType proof)

end JanetCartan.RevisedUniform.OriginalStepThresholdsTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.T
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.T_ge_two
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.T_reaches
