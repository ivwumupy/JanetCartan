module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeSplit
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
/-! The B in the actual complete-source amplitude split is the SAME unscaled
baseline data whose native profile is transferred in task 112. This is an exact
function identity, independent of source, truncation and point; the original
outer sample and phase are not replaced (`main:prop:pairs`). -/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentityTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "identify_original_complete_baseline" : command => liftTermElabM do
  withActualSelectedSourceWave fun p _ _ literal _ _ _ => do
    unless literal.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.field 69 do
      throwError "actual baseline identity: changed original complete wave"
    let i := p[52]!
    let index ← inferType i
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual baseline identity: not the original outer sample type"
    let sa := index.getAppArgs
    let row := Expr.proj ``Sigma 0 i
    let sampleValue := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 1 i)
    let color := app `JanetCartan.SeparatedSampling.color #[sa[1]!,Expr.proj ``Prod 0 sampleValue]
    let native := p[:50].toArray ++ #[row,color] ++ literal.getAppArgs[64:68].toArray
    unless native.size == 56 do throwError "actual baseline identity: changed native52/outer4 ABI"
    let B := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.baselineAmplitude p
    let Bnative := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.baselineAmplitude native
    let type ← instantiateMVars (← mkForallFVars p (← mkEq B Bnative))
    let value ← instantiateMVars (← mkLambdaFVars p (← mkEqRefl B))
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "actual baseline identity: unresolved exact original baseline"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentity.baseline_eq_actual_baseline
    liftM <| IO.eprintln "actual baseline identity: kernel checking exact unscaled B53=B56"
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    addDocStringCore name "The actual complete-wave physical baseline amplitude is precisely the same unscaled native52/outer4 baseline, with original phase and sample retained (main:prop:pairs, main:eq:mean-final-amplitude)."
    liftM <| IO.eprintln "actual baseline identity: kernel passed exact unscaled B53=B56"
end JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentityTemplate
end
