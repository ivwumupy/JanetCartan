module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparison
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate

/-!
# The actual comparison cost before every current history

Restrict the already constructed `actualCcompare` to its true static inputs.
This is its literal `OriginalComparison.Ccompare` body, not a new choice of
comparison constant. The closure check rejects any dependence on the initial
frequency, its threshold evidence, the stage or the preceding history.
The finite normalized global transport sum consumes this cost
(`app:ch_mean_pairs:eq:mean-stage-normal-errors`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearComparisonBudgets
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearComparison
private def original := `JanetCartan.PhysicalNormalInverse.OriginalComparison

private def save (short : Name) (xs : Array Expr) (term : Expr) (data := false)
    (goal : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match goal with | some g => pure g | none => inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original comparison budget {short}: nonstatic or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "original comparison budget {short}: missing producers {missing.toList}"
  let name := root ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The literal original comparison budget on prehistory44 and the original row; no frequency, threshold-reached evidence, history or sampled shift enters this cost (app:ch_mean_pairs:eq:mean-stage-normal-errors)."
  logInfo m!"static original comparison budget {short}: {xs.size} inputs"
  return mkAppN (mkConst name) xs

elab "publish_original_mean_static_comparison_budget " mode:num : command => liftTermElabM do
  let info ← getConstInfo (root ++ `actualCcompare)
  let some body := info.value? (allowOpaque := true)
    | throwError "original comparison budget: actual cost body unavailable"
  forallBoundedTelescope info.type (some 50) fun xs _ => do
    unless xs.size == 50 do throwError "original comparison budget: native50 changed"
    lambdaTelescope (body.beta xs).headBeta fun ix c => do
      unless ix.size == 1 && c.isAppOfArity (original ++ `Ccompare) 46 do
        throwError "original comparison budget: literal original Ccompare46 changed"
      let static := xs[:44].toArray ++ ix
      if mode.getNat == 0 then
        discard <| save `Ccompare static c true
      else if mode.getNat == 1 then
        let positive := mkAppN (mkConst (original ++ `positive)) c.getAppArgs
        let named := mkAppN (mkConst (root ++ `Ccompare)) static
        let target := (← inferType positive).replace fun e =>
          if e == c then some named else none
        discard <| save `Ccompare_positive static positive false (some target)
      else if mode.getNat == 2 then
        let actual := mkAppN (mkConst (root ++ `actualCcompare)) (xs ++ ix)
        let named := mkAppN (mkConst (root ++ `Ccompare)) static
        discard <| save `actualCcompare_eq (xs ++ ix) (← mkEqRefl c) false
          (some (← mkEq actual named))
      else throwError "original comparison budget: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalMeanLinearComparisonBudgets
end

publish_original_mean_static_comparison_budget 0
publish_original_mean_static_comparison_budget 1
publish_original_mean_static_comparison_budget 2

#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearComparison.Ccompare
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearComparison.Ccompare_positive
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearComparison.actualCcompare_eq
