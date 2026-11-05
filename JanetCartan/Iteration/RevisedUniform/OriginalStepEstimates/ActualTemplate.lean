module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ConditionedTemplate
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.CostPublicationTemplate
public meta import Lean

/-!
# Substitute the original primary strain into the original physical step

The execution leaf imports `step_of_primary_strain` and the checked original
primary strain before running these commands. The actual coefficient depends
only on the fixed dimension/metric and accuracy. The actual step takes only
the original metric, history, defect and numerical gates.

No additional construction, success record or analytic assumption is added.
The consumer is `OriginalUniformCorrection.uniformHistoryCorrection` for
`main:thm:step` and `main:prop:current-scale`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepActualTemplate

open Lean Meta Elab Command
open OriginalStepEstimatesTemplate OriginalUniformCorrectionTemplate
open OriginalStepCostPublicationTemplate

private def root := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def strainRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
private def uniformRoot := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def tail (p : Expr) (i : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) i p
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0 (tail p i)
private def checkedProducer (name : Name) : MetaM Unit := do
  let _ ← getConstInfo name
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual original step: unfinished producer {name}: {axioms}"

private def save (key : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  unless p.size == 21 do
    throwError "actual original step: an extra original-data input entered {key}/{p.size}"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual original step: unresolved or extra operand in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "actual original step: unavailable original metadata {missing.toList}"
  if key == `step then
    for producer in #[root ++ `step_of_primary_strain,root ++ `primary_strain_input_of_raw,
        strainRoot ++ `strain_bound,
        uniformRoot ++ `primaryGraphOperator_reached] do
      unless value.getUsedConstants.contains producer do
        throwError "actual original step: the original producer was not instantiated {producer}"
  let name := root ++ key
  if (env.find? name).isSome then
    throwError "actual original step: duplicate declaration {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Checking actual original physical step {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original-data physical step and its common coefficient, with the exact OriginalSelectedPrimaryStrain producer substituted into the already checked original mean/pair/smoothing/norm construction. The coefficient is fixed before every history and target dilation; the same Schwartz increment has the exact fixed Fourier band, displacement loss and cubic error. Only original metric/history/defect and numerical inputs remain (main:thm:step; main:prop:current-scale)."
  checkedProducer name
  logInfo m!"PASS actual original physical step {key}/{p.size}: {← collectAxioms name}"

/-- Apply the actual primary strain at the same selected52 and requested
Picard count; publish exactly stage19 plus the two final numerical reaches. -/
elab "prove_actual_original_step" : command => liftTermElabM do
  checkedProducer (root ++ `step_of_primary_strain)
  checkedProducer (root ++ `primary_strain_input_of_raw)
  checkedProducer (strainRoot ++ `strain_bound)
  checkedProducer (uniformRoot ++ `primaryGraphOperator_reached)
  checkedProducer (root ++ `C)
  withSelectedStage fun stage => do
    unless stage.stageParameters.size == 19 do
      throwError "actual original step: original stage19 changed"
    let n := mkApp (mkConst ``Nat.succ) stage.dimension[0]!
    let k := stage.stageParameters[16]!
    let count ← originalStrainCount n k
    let Qp := app (uniformRoot ++ `primaryOrder) #[n,k]
    let Cstrain := originalStrainCost stage.selected33 n k count
    let one ← mkNumeral (mkConst ``Real) 1
    let R0 := stage.stageParameters[7]!
    let Tpair := app `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial.Tpair
      (stage.dimension.push one)
    withLocalDeclD `hInitialPair (← mkAppM ``LE.le #[Tpair,R0]) fun hPair => do
      let T := app (root ++ `T) (stage.parameters.push k)
      withLocalDeclD `hT (← mkAppM ``LE.le #[T,stage.scale]) fun hT => do
        let reaches := app `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial.initial_reaches
          (stage.dimension ++ #[one,R0,hPair])
        let initial := app `JanetCartan.RevisedUniform.OriginalFinalReach.initial_gates
          (stage.dimension ++ #[R0,part reaches 0])
        let facts := app `JanetCartan.RevisedUniform.iteration_scale_power_facts
          #[R0,part initial 0,stage.stageParameters[9]!,k,n]
        let hOperator := app (uniformRoot ++ `primaryGraphOperator_reached)
          (stage.dimension ++ #[one,R0,hPair])
        let hDeltaNonneg ← mkAppM ``le_of_lt #[part facts 1]
        let strainArgs := stage.selected52 ++
          #[tail initial 7,hOperator,count,Qp,stage.delta,hDeltaNonneg]
        let originalStrain := app (strainRoot ++ `strain_bound) strainArgs
        let hStrain := app (root ++ `primary_strain_input_of_raw)
          (strainArgs.push originalStrain)
        let proof := app (root ++ `step_of_primary_strain)
          (stage.parameters ++ #[Cstrain] ++ stage.stageParameters[7:].toArray ++
            #[hPair,hT,hStrain])
        let originalType ← inferType proof
        unless originalType.isAppOfArity ``Exists 2 do
          throwError "actual original step: an analytic step input remains"
        let earlyCost := app (root ++ `C_of_primary_strain) (stage.parameters ++ #[k,Cstrain])
        let namedCost := app (root ++ `C) (stage.parameters.push k)
        let target := originalType.replace fun e => if e == earlyCost then some namedCost else none
        unless target.getUsedConstants.contains (root ++ `C) do
          throwError "actual original step: the common early coefficient was lost"
        save `step (stage.stageParameters ++ #[hPair,hT]) proof target

end JanetCartan.RevisedUniform.OriginalStepActualTemplate
end
