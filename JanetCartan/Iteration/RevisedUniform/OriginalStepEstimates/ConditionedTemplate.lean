module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.AssembleTemplate
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.StrainInput
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Thresholds
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Smoothing
public meta import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SelectedInput
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Original-data finite step with the primary strain input explicit

Independent deduction from the precise outstanding primary-strain bound.
Every mean, pair, smoothing, norm, current-map and numerical input is supplied
by its actual original producer. The primary constant is fixed before the
history, and its original producer is `OriginalSelectedPrimaryStrain`.
This is not the unconditional uniform correction or Theorem 1.1.

The execution leaf imports the checked mean and pair profile/core producers
before running these commands (`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepConditionedTemplate

open Lean Meta Elab Command
open OriginalStepEstimatesTemplate OriginalUniformCorrectionTemplate

private def root := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def tail (p : Expr) (i : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) i p
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0 (tail p i)
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | value => value
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual conditioned step: missing original data {key}"
  pure (head (value.beta p))
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

private def save (key : Name) (params : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual conditioned step: an extra or unresolved operand entered {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "actual conditioned step: missing original metadata {missing.toList}"
  if key == `step_of_primary_strain then
    for producer in #[root ++ `increment_estimates_of_source_profiles,
        `JanetCartan.RevisedUniform.OriginalUniformCorrection.smoothing_bounds,
        `JanetCartan.RevisedUniform.OriginalSelectedMeanStep.mean_error_le_requested_precision,
        `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles.physicalMean_sobolev_profile,
        `JanetCartan.PhysicalPairs.OriginalSelectedPairCore.metric_lag,
        `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates.size,
        `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.L2_profiles] do
      unless value.getUsedConstants.contains producer do
        throwError "actual conditioned step: original producer not applied {producer}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Checking original-data step with explicit primary strain {key}/{params.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original-data physical step with ONLY the exact primary-strain coefficient and bound still explicit. The coefficient precedes the history; all original complete-forcing mean, pair, smoothing, norm, frame, order and cutoff producers are applied internally on the same sample and Picard count. The actual producer OriginalSelectedPrimaryStrain must still instantiate this input before claiming UHC/Main (main:thm:step; main:prop:current-scale)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual conditioned step: nonstandard axioms {axioms}"
  logInfo m!"PASS original-data step with explicit primary strain {key}/{params.size}: {axioms}"

elab "prove_original_step_of_primary_strain" : command => liftTermElabM do
  withSelectedStage fun stage => do
    unless stage.stageParameters.size == 19 do
      throwError "actual conditioned step: original stage19 changed"
    let selected := stage.selected52
    let native := stage.native50
    let raw := `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget
    let source ← bodyAt raw selected
    unless source.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
      throwError "actual conditioned step: original smoothed source changed"
    let rawSourceArgs := source.getAppArgs
    let n := app ``Nat.succ #[stage.dimension[0]!]
    let targetDimension := app `JanetCartan.embeddingDimension #[n]
    unless ← isDefEq n rawSourceArgs[0]! do
      throwError "actual conditioned step: original source dimension changed"
    unless ← isDefEq targetDimension rawSourceArgs[1]! do
      throwError "actual conditioned step: original target dimension changed"
    let a := (rawSourceArgs.set! 0 n).set! 1 targetDimension
    let k := selected[49]!
    let Qp := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.primaryOrder #[n,k]
    let Qm := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.meanOrder #[n,k]
    let accuracy ← termWith [(`q,Qm)] "(q : ℝ) + 1"
    let count := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionSteps #[n,accuracy]
    let P := app `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
      (selected ++ #[count,a[6]!])
    let rawP ← bodyAt `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field P.getAppArgs
    unless rawP.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary 53 do
      throwError "actual conditioned step: changed original complete-source primary"
    let J := rawP.getAppArgs[50]!
    unless J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
      throwError "actual conditioned step: original J changed"
    let one ← mkNumeral (mkConst ``Real) 1
    let Tpair := app `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial.Tpair
      (stage.dimension.push one)
    withLocalDeclD `Cstrain (mkConst ``Real) fun Cstrain => do
      withLocalDeclD `hInitialPair (← mkAppM ``LE.le #[Tpair,native[44]!]) fun hPair => do
        let thresholdArgs := stage.parameters.push k
        let T := app (root ++ `T) thresholdArgs
        withLocalDeclD `hT (← mkAppM ``LE.le #[T,stage.scale]) fun hT => do
          let reached := app (root ++ `T_reaches) (thresholdArgs ++ #[stage.scale,hT])
          let smoothing := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.smoothing_bounds
            (stage.stageParameters.push (part reached 1))
          let smootherArgs := stage.parameters ++ #[selected[47]!,selected[48]!]
          let Csmall := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingSmall smootherArgs
          let Cfast := app `JanetCartan.RevisedUniform.OriginalUniformCorrection.CsmoothingHigh smootherArgs
          let strainType := app (root ++ `primary_strain_input)
            (selected ++ #[count,Qp,a[6]!,Cstrain])
          withLocalDeclD `hPrimaryStrain strainType fun hStrain => do
            let proof ← originalStepProof stage.dimension selected native a J
              hPair (part reached 2) (part reached 3) (tail reached 4)
              Csmall Cfast (.proj ``And 0 smoothing) (.proj ``And 1 smoothing) Cstrain hStrain
            let originalType := head (← inferType proof)
            unless originalType.isAppOfArity ``And 2 do
              throwError "actual conditioned step: original step did not return its three estimates"
            let some U := originalType.find? (·.isAppOfArity `JanetCartan.RevisedStage.increment 5)
              | throwError "actual conditioned step: actual cutoff witness missing"
            let namedCost := app (root ++ `C_of_primary_strain) (stage.parameters ++ #[k,Cstrain])
            let boundType := originalType.replace fun e =>
              if e.isAppOfArity (root ++ `finalConstant) 4 then some namedCost else none
            unless boundType.getUsedConstants.contains (root ++ `C_of_primary_strain) do
              throwError "actual conditioned step: common early coefficient lost"
            let space ← inferType U
            let .sort level ← whnf (← inferType space)
              | throwError "actual conditioned step: original Schwartz output is not a type"
            let predicate ← withLocalDeclD `U space fun u => do
              mkLambdaFVars #[u] (boundType.replace fun e => if e == U then some u else none)
            let target := mkApp2 (mkConst ``Exists [level]) space predicate
            let value := mkAppN (mkConst ``Exists.intro [level]) #[space,predicate,U,proof]
            let params := stage.parameters ++ #[Cstrain] ++ stage.stageParameters[7:].toArray ++
              #[hPair,hT,hStrain]
            unless params.size == 23 do throwError "actual conditioned step: extra source input appeared"
            save `step_of_primary_strain params value target

end JanetCartan.RevisedUniform.OriginalStepConditionedTemplate
end
