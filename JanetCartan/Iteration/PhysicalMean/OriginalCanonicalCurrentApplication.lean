module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
public meta import Lean

/-!
# The actual global mean inverse on the same native50 history

The positive scalar already contains `NativeAdmission.labels` on the global
native39. Reading that exact prefix preserves the one Vop, complete measured
normal and Q0. The per-row comparison Current49 is deliberately not used.
Consumer: `OriginalInverse.canonicalSourceIterate`
(`new:sec:mean-source-equation`, `new:eq:source-bound`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalCurrentApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

/-- Exact global native39 already used by the unchanged positive scalar.
The last two label arguments are the row and label point; neither is selected
or allowed to leak into this global inverse prefix. -/
def nativeCurrentArguments (d : ActualRow) : MetaM (Array Expr) := do
  let name := `JanetCartan.PhysicalBackground.NativeAdmission.labels
  let some labels := d.mean70[54]!.find? (·.isAppOf name)
    | throwError "actual global mean current: original positive labels missing"
  unless labels.isAppOfArity name 41 do
    throwError "actual global mean current: changed native39/row/label-point spine"
  let native := labels.getAppArgs[:39].toArray
  for index in [:native.size] do
    if (native[index]!.find? (fun e => e == d.row)).isSome || native[index]!.hasLooseBVars then
      throwError "actual global mean current: row or label point leaked into entry {index}"
  return native

/-- A read-only renaming of the exact global native39 onto an already opened
native50. This does not replay a threshold, choose a row, or choose a Vop. -/
def withCurrentAt (xs : Array Expr) (next : Array Expr → MetaM Unit) : MetaM Unit := do
  unless xs.size == 50 do throwError "actual global mean current: expected native50"
  withTransparency .reducible <| withActualRow fun d => do
    let native ← nativeCurrentArguments d
    let old := d.parameters[:50].toArray
    next (native.map (fun e => e.replaceFVars old xs))

private def save (short : Name) (xs : Array Expr) (term : Expr) (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual global mean current: missing producer constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual global mean current: unclosed or extra input in {short}"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalCurrent ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME global admission39 current on the actual native50 history, decoded from the unchanged positive scalar. No per-row comparison inverse, new Vop, density, source or threshold reach (new:sec:mean-source-equation)."
  logInfo m!"actual global mean current {short}: native50 from SAME row-free admission39"

elab "construct_actual_canonical_current " mode:num : command => liftTermElabM do
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let native ← nativeCurrentArguments d
    let specifications := #[
      (`coefficient,39,true), (`measurement,21,true), (`source,21,true),
      (`exterior,21,true), (`carriers,39,true), (`Q0,39,true),
      (`coefficient_smooth,39,false), (`measurement_smooth,21,false),
      (`source_smooth,21,false), (`exterior_smooth,21,false),
      (`source_regular,39,false)]
    let index := mode.getNat
    unless index < specifications.size do throwError "actual global mean current: unknown field"
    let (name,count,data) := specifications[index]!
    let value := mkAppN (mkConst
      (`JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current ++ name)) native[:count].toArray
    save name xs value data

end JanetCartan.PhysicalMean.OriginalCanonicalCurrentApplication
end
