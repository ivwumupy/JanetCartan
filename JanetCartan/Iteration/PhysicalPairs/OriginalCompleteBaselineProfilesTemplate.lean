module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNativeProfiles
/-! # The genuine baseline profile at every actual selected source node

Every original SampleIndex carries nonzero OUTER sampling weight. Feed that
literal proof to the native baseline producer, and identify its amplitude with
the B in the same actual complete-wave split. There is no inner angular gate,
no zeroed-wave replacement, and no source, L or sample in Cbaseline44
(`main:prop:pairs`, `main:eq:mean-final-amplitude`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteBaselineProfilesTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "prove_original_complete_baseline_profile" : command => liftTermElabM do
  withActualSelectedSourceWave fun p _ _ _ _ _ _ => do
    let identity := app `JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentity.baseline_eq_actual_baseline p
    let ty ← inferType identity
    unless ty.isAppOfArity ``Eq 3 do throwError "actual baseline profile: complete baseline identity changed"
    let B := ty.getAppArgs[1]!
    let native := ty.getAppArgs[2]!
    unless native.isAppOfArity `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.baselineAmplitude 56 do
      throwError "actual baseline profile: native outer56 changed"
    let i := p[52]!
    let index ← inferType i
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual baseline profile: original SampleIndex changed"
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.original_sample_weight_ne_zero [.zero])
      (index.getAppArgs.push i)
    let proof := app `JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles.baseline_profile (native.getAppArgs.push hμ)
    let target := (← inferType proof).replace fun e => if e == native then some B else none
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "actual baseline profile: a new analytic or sample input escaped"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.PhysicalPairs.OriginalCompleteBaselineProfiles.baseline_profile
    IO.println "Kernel checking actual selected complete-wave B53 profile"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "Every actual original selected SampleIndex automatically admits the SAME complete-wave baseline B53 to the original native outer57 producer: whole-chart smoothness and Cbaseline44(j)*T^j jets, without any inner angular gate or added analytic premise (main:prop:pairs; main:eq:mean-final-amplitude)."
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual selected baseline profile: nonstandard axioms {axioms}"
    logInfo m!"actual selected complete-wave B53 profile: {axioms}"
end JanetCartan.PhysicalPairs.OriginalCompleteBaselineProfilesTemplate
end
