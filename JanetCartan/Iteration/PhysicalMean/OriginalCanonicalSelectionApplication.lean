module

public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean

/-!
# Name the one selected original shift

The data operators retain arbitrary shifts for the trial family. Closed
estimates and the final source run all reuse this one named choice from the
unchanged `exists_on_original_history`50, with its literal predicate. No second
event, row, cutoff or selector is chosen (`new:sec:order-of-choices`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalSelectionApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def save (short : Name) (xs : Array Expr) (term : Expr) (data : Bool)
    (expected : Option Expr := none) : MetaM Unit := do
  let result ← match expected with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars xs result)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "original single selection: missing constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original single selection: extra/unresolved input in {short}"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSelection ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The ONE named shift or its exact event predicate from the SAME original native50 event. All closed source/normal/mean estimates reuse this choice; trial-family data remain defined at arbitrary shifts (new:sec:order-of-choices)."
  logInfo m!"original single selected {short}: native50, exact original event and no reselection"

elab "construct_original_canonical_selection " mode:num : command => liftTermElabM do
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let existsProof := mkAppN (mkConst
      `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.exists_on_original_history) xs
    let result ← whnf (← inferType existsProof)
    unless result.isAppOfArity ``Exists 2 do
      throwError "original single selection: actual one-shift event changed"
    match mode.getNat with
    | 0 => save `shift xs (← mkAppM ``Classical.choose #[existsProof]) true
    | 1 =>
      let ξ := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
      let predicate := result.getAppArgs[1]!
      save `event xs (← mkAppM ``Classical.choose_spec #[existsProof]) false
        (some (predicate.beta #[ξ]))
    | _ => throwError "original single selection: unknown field"

end JanetCartan.PhysicalMean.OriginalCanonicalSelectionApplication
end
