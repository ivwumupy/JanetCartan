module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCompletedResidual
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourcePicardPrecision
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The released full selected forcing on the original projected core

Instantiate the original completed residual with the literal selected measured
target and its full three-term source. The second theorem uses exactly the
forcing-DATA Picard run, never the old background-only iterate. The target-value
and geometric normal-completion joins remain separate from this algebraic
identity (`new:eq:reduced-mean-identity`, `main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedCoreResidual
open Lean Meta Elab Command

private def ns := `JanetCartan.PhysicalMean.OriginalSelectedCoreResidual
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def bodyAt (name : Name) (args : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo name).value? | throwError "selected core: missing {name} body"
  return (mkAppN body args).headBeta

private def withSelected (next : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (forcing ++ `selectedFullSource)).type (some 52) fun p _ => do
    unless p.size == 52 do throwError "selected core: changed full selected source52"
    let raw ← bodyAt (forcing ++ `selectedFullSource) p
    unless raw.isAppOfArity (forcing ++ `completeSource) 4 do
      throwError "selected core: full source is not the actual three signed components"
    let a := raw.getAppArgs
    unless a[1]!.isAppOfArity (forcing ++ `leadingMean) 50 &&
        a[2]! == app (forcing ++ `selectedMeasuredTarget) p &&
        a[3]!.isAppOfArity (forcing ++ `selectedSampleSelf) 50 do
      throwError "selected core: replaced leading mean, measured target, or original self"
    let native50 := a[1]!.getAppArgs
    unless a[3]!.getAppArgs == native50 do throwError "selected core: another sample/history in the full self"
    next p native50 a[2]! (app (forcing ++ `selectedFullSource) p)

private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  unless p.size == 57 do throwError "selected core: expected selected52 plus five data/core arguments"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "selected core: missing original producers {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "selected core: extra or unresolved input"
  unless (type.find? (·.isAppOf (forcing ++ `selectedFullSource))).isSome &&
      (type.find? (·.isAppOf (forcing ++ `selectedMeasuredTarget))).isSome do
    throwError "selected core: full selected source or actual target disappeared"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The original projected physical core identity with the literal selectedFullSource52 and selectedMeasuredTarget52, actual affine cancellation, SAME selected E/Q/global inverse and unchanged core. No partial forcing, replacement sample, source profile or full tensor cancellation assumption (new:eq:reduced-mean-identity)."
  logInfo m!"selected full-source core {key}/57: original source, target, selected operators and core"

run_elab withSelected fun p native target full => do
  withLocalDeclNoLocalInstanceUpdate `cutoff .default (mkConst ``Nat) fun L => do
    let stem := app `JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual.residual_eq_projected_core_defect
      (native ++ #[L,target])
    forallBoundedTelescope (← inferType stem) (some 4) fun tail _ => do
      unless tail.size == 4 do throwError "selected core: changed source/point/core/component tail"
      let proof := mkAppN stem tail
      let type ← inferType proof
      let some raw := type.find? (·.isAppOfArity (forcing ++ `completeSource) 4)
        | throwError "selected core: missing complete forcing in residual"
      unless raw.getAppArgs[1]! == app (forcing ++ `leadingMean) native &&
          raw.getAppArgs[2]! == target && raw.getAppArgs[3]! == app (forcing ++ `selectedSampleSelf) native do
        throwError "selected core: original complete source did not match literally"
      let type := type.replace fun e => if e == raw then some full else none
      save `source_residual_eq_projected_core_defect (p ++ #[L] ++ tail) proof type

run_elab withSelected fun p native _ full => do
  withLocalDeclNoLocalInstanceUpdate `cutoff .default (mkConst ``Nat) fun L => do
    withLocalDeclNoLocalInstanceUpdate `steps .default (mkConst ``Nat) fun steps => do
      let run := app (source ++ `selected_iterateWithForcing) (native ++ #[L,full,steps])
      let stem := app (ns ++ `source_residual_eq_projected_core_defect) (p ++ #[L,run])
      forallBoundedTelescope (← inferType stem) (some 3) fun tail _ => do
        unless tail.size == 3 do throwError "selected core: changed point/core/component tail"
        let proof := mkAppN stem tail
        let type ← inferType proof
        let some raw := type.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sourceResidual 7)
          | throwError "selected core: missing exact forcing-DATA residual"
        let residual := app (source ++ `selected_residualWithForcing) (native ++ #[L,full,steps])
        let type := type.replace fun e => if e == raw then some residual else none
        save `picard_residual_eq_projected_core_defect (p ++ #[L,steps] ++ tail) proof type

end JanetCartan.PhysicalMean.OriginalSelectedCoreResidual
end
