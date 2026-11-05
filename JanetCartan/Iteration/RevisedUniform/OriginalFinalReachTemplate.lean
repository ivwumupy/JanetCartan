module
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalReach
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSourceProfiles
public meta import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
public meta import Lean

/-! # Exact dimension-only specialization of every initial mean gate

Reuse the unchanged original dimension-only selection. No metric, accuracy,
Picard depth, source or history can enter the initial reach
(`new:sec:order-of-choices`, `main:prop:mean`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.RevisedUniform.OriginalFinalReachTemplate
open Lean Meta Elab Command
open OriginalSelectedPrehistoryTemplate (withDimensionStatic)
def root := `JanetCartan.RevisedUniform.OriginalFinalReach
def fixedThresholds : Array (Name × Name) := #[
  (`Scomp, `JanetCartan.PhysicalMean.OriginalNormalCompletionProfiles.Scomp),
  (`Serror, `JanetCartan.PhysicalMean.OriginalMeanErrorTransfer.Serror),
  (`Sbase, `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.Sbase),
  (`Sbuffer, `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles.Sbuffer),
  (`SfullW, `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.SfullW),
  (`Saux, `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Saux)]
def save (key : Name) (dh : Array Expr) (value target : Expr) (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars dh target)
  let value ← instantiateMVars (← mkLambdaFVars dh value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "final initial reach: metric, accuracy, history or unresolved input escaped {key}"
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "final initial reach: missing {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Literal dimension-only specialization of the SAME original native44 threshold. Fixed before metric dilation, accuracy, finite Picard depth, smoothing and all histories (new:sec:order-of-choices; main:prop:mean)."
  logInfo m!"actual final initial reach {key}/{dh.size}: dimension-only SAME native44"

def publishThreshold (index : Nat) : MetaM Unit := do
  unless index < fixedThresholds.size do throwError "final initial reach: unknown fixed gate"
  withDimensionStatic fun dh _ _ native => do
    let (key,name) := fixedThresholds[index]!
    save key dh (mkAppN (mkConst name) native) (mkConst ``Real) true

def publishSourceAuxPaid : MetaM Unit := do
  withDimensionStatic fun dh _ _ native => do
    let literal := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Saux) native
    let old := mkAppN (mkConst `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.Tref) dh
    let bound := mkAppN (mkConst `JanetCartan.RevisedUniform.OriginalSelectedPrehistory.Saux_le_Tref) dh
    let named := mkAppN (mkConst (root ++ `Saux)) dh
    unless ← isDefEq literal named do throwError "final initial reach: changed actual high-source guard"
    let target ← mkAppM ``LE.le #[named,old]
    save `Saux_le_oldTref dh bound target false
end JanetCartan.RevisedUniform.OriginalFinalReachTemplate
end
