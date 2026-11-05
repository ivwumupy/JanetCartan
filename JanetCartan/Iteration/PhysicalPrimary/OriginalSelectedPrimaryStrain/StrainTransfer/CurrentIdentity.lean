module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeCurrentStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeCurrentStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
import all JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
import all JanetCartan.Iteration.PhysicalInitialization.CurrentLeading
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The original response and raw-source current are the same finite map

The graph adapter already proves that its full response uses the original
finite history map. The raw-source current is the same map through the saved
`OriginalLocalWaves.F` and `CurrentLeading.History.F` definitions. Apply that
checked identity to the separately retained native53 equality statement.

Consumer: the current transport in `StrainTransfer.NativeTensor`, hence the
same-node source-discrepancy bound (`main:eq:lag-strain` and
`main:eq:primary-strain` in paper-v2). The original current, source, history,
sample and parameter order are unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.CurrentIdentity

open Lean Meta Elab Command

private def root :=
  `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer

private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "original current identity: missing saved body {info.name}"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta
    e.getAppArgs).headBeta

run_meta do
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    unless p.size == 53 do
      throwError "original current identity: original native53 changed"
    let target := app (root ++ `native_current_eq_statement) p
    let equality ← bodyAt target
    unless equality.isAppOfArity ``Eq 3 do
      throwError "original current identity: the retained statement is not an equality"
    let full := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.F c.weak
    let raw := (← bodyAt c.tensorField).getAppArgs[2]!
    unless equality.getAppArgs[1]! == full && equality.getAppArgs[2]! == raw do
      throwError "original current identity: different response or raw-source current"
    unless raw.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.F 53 do
      throwError "original current identity: original raw current wrapper changed"
    let history ← bodyAt raw
    unless history.isAppOfArity
        `JanetCartan.PhysicalInitialization.CurrentLeading.History.F 37 do
      throwError "original current identity: original history wrapper changed"
    let finite ← bodyAt history
    unless finite.isAppOfArity `JanetCartan.RevisedGlobal.finiteMap 5 do
      throwError "original current identity: original finite history map changed"
    let proof := app `JanetCartan.PhysicalSampling.OriginalGraphResponse.same_finite_map
      c.graph
    let original ← inferType proof
    unless original.isAppOfArity ``Eq 3 && original.getAppArgs[1]! == full &&
        original.getAppArgs[2]! == finite do
      throwError "original current identity: the checked graph identity has different operands"
    let early ← mkLambdaFVars p[:50].toArray finite
    if early.hasFVar || early.hasLooseBVars then
      throwError "original current identity: the finite map acquired late source or sample data"
    let type ← instantiateMVars (← mkForallFVars p target)
    let proof ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type, proof] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
          e.hasLooseBVars || e.hasSorry then
        throwError "original current identity: unresolved native53 input"
      let missing := e.getUsedConstants.filter fun name => (env.find? name).isNone
      unless missing.isEmpty do
        throwError "original current identity: missing original metadata {missing}"
    let (type, proof) := Lean.ShareCommon.shareCommon (type, proof)
    let name := root ++ `native_current_eq
    IO.println "Kernel checking original response/raw-source current identity/53"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name, levelParams := [], type, value := proof})
      (forceExpose := true)
    addDocStringCore name "The SAME OriginalFullResponse.F weak38 equals the current in the actual raw-source body, at the unchanged native53 interface. Apply the original graph same_finite_map identity to the separately checked equality statement; the raw current unfolds through its two saved history definitions. No analytic hypothesis is added. Consumer: the current transport in NativeTensor (main:eq:lag-strain; main:eq:primary-strain)."
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "original current identity: nonstandard axioms {axioms}"
    logInfo m!"PASS original response/raw-source current identity/53: {axioms}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.CurrentIdentity
end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.native_current_eq
