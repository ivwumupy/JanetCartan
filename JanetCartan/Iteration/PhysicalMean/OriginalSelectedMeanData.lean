module

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalResidual
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Literal fields of the original full-source Picard mean

Name, without selecting again, the normalized target, full initialized field,
full sampled self tensor, and their single normal completion already present
in the checked actual physical residual. These are the data consumed by the
original geometric error transfer and physical cutoff construction
(`new:eq:qT-identity`, `main:eq:mean-normal-field`, `main:prop:mean`).
No source/field estimate, target regularity or mean success is an input.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanDataTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def original := `JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual.picard_residual_eq_reduced_physical_residual
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual mean data: unavailable original {key}"
  return (value.beta p).headBeta

/-- Read the existing selected56 residual identity and its exact native50/39.
No original frame, inverse, current, sample or source is chosen here. -/
def withActualSelectedFields
    (next : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo original).type (some 56) fun p type => do
    unless p.size == 56 && type.isAppOfArity ``Eq 3 do
      throwError "actual mean data: changed actual selected56"
    let rhs := type.getAppArgs[2]!
    unless rhs.isAppOfArity `JanetCartan.PhysicalMean.reducedPhysicalResidual 7 do
      throwError "actual mean data: changed normalized physical residual"
    let fields := rhs.getAppArgs
    unless fields[4]!.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
      throwError "actual mean data: lost the literal normalized physical target"
    let full ← bodyAt (forcing ++ `selectedFullSource) p[:52].toArray
    unless full.isAppOfArity (forcing ++ `completeSource) 4 do
      throwError "actual mean data: replaced the same complete forcing"
    let leading := full.getAppArgs[1]!
    unless leading.isAppOfArity (forcing ++ `leadingMean) 50 do
      throwError "actual mean data: changed original native50"
    let native := leading.getAppArgs
    let meanEq ← inferType (app (forcing ++ `physicalAffineMean_eq_original) native)
    let mean := meanEq.getAppArgs[2]!
    unless mean.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.physicalMean 39 do
      throwError "actual mean data: changed original native39"
    next p fields native mean.getAppArgs (app original p)

private def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun k => (env.find? k).isNone)
    unless missing.isEmpty do throwError "actual mean data: missing {missing.toList}"
    for forbidden in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate] do
      if e.getUsedConstants.contains forbidden then throwError "actual mean data: background-only forcing run"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual mean data: extra or unresolved input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The literal SAME selected full-source Picard mean data: original normalized target, initialized base plus source field, full sampled self, and one normal completion. No field estimate, new choice or analytic success premise (main:eq:mean-normal-field; new:eq:qT-identity)."
  logInfo m!"actual selected mean data {key}/{p.size}"

elab "define_original_selected_mean_data " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "actual mean data: unknown definition mode"
  withActualSelectedFields fun p f _ _ proof => do
    let selected := p[:52].toArray
    let stage := p[:54].toArray
    match mode.getNat with
    | 0 => save `normalizedTarget selected f[4]! true
    | 1 => save `initializedField stage f[3]! true
    | 2 => save `fullSampledSelf stage f[5]! true
    | 3 =>
      let value := app `JanetCartan.CurrentMean.completedMeanField
        #[f[0]!,f[1]!,f[2]!,app (root ++ `initializedField) stage,
          app (root ++ `normalizedTarget) selected,app (root ++ `fullSampledSelf) stage]
      save `completedMean stage value true
    | _ =>
      let type ← inferType proof
      let named := app `JanetCartan.PhysicalMean.reducedPhysicalResidual
        #[f[0]!,f[1]!,f[2]!,app (root ++ `initializedField) stage,
          app (root ++ `normalizedTarget) selected,app (root ++ `fullSampledSelf) stage,f[6]!]
      save `residual_eq_reduced_physical_residual p proof false
        (some (← mkEq type.getAppArgs[1]! named))

end JanetCartan.PhysicalMean.OriginalSelectedMeanDataTemplate
end

define_original_selected_mean_data 0
define_original_selected_mean_data 1
define_original_selected_mean_data 2
define_original_selected_mean_data 3
define_original_selected_mean_data 4
