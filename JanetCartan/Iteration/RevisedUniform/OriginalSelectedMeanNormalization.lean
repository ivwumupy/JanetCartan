module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalSmoothing.Basic
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# The selected mean target is the same smoothed metric defect divided by b²

Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles.hmean`
in `main:thm:step`. The actual selected52 target is identified with the literal
physical finite-moment smoother, at the same domain, history, target, smoothing
order, current scale and revised forcing amplitude. No estimate, new selector,
mean-success premise or field replacement is introduced. The full-self identity
and the actual residual bounds remain their separate already-named producers.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.RevisedUniform.OriginalSelectedMeanNormalization
open Lean Meta Elab Command
run_cmd liftTermElabM do
  PhysicalMean.OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f _ _ _ => do
    unless f[4]!.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
      throwError "selected mean normalization: original normalized source changed"
    let selected := p[:52].toArray
    let sourceArgs := f[4]!.getAppArgs
    let proof := mkAppN (mkConst `JanetCartan.PhysicalSmoothing.normalizedSource_eq) sourceArgs
    let eqType ← inferType proof
    unless eqType.isAppOfArity ``Eq 3 && eqType.getAppArgs[1]! == f[4]! do
      throwError "selected mean normalization: not the literal smoother normalization"
    let named := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget) selected
    let target ← mkEq named eqType.getAppArgs[2]!
    let type ← instantiateMVars (← mkForallFVars selected target)
    let value ← instantiateMVars (← mkLambdaFVars selected proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "selected mean normalization: missing original witness {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "selected mean normalization: extra Picard/index/point or analytic input escaped"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.RevisedUniform.OriginalSelectedMeanNormalization.normalizedTarget_eq_smoothedDefect
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The genuine selected52 normalized mean target is exactly the SAME physical finite-moment defect divided by the square of b=delta*R^RevisedScales.forcingExponent n. Original domain, target, history, current scale and smoothing order are preserved; no new estimate or analytic premise (main:thm:step; main:lem:smoothing)."
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "selected mean normalization: nonstandard axioms {axioms}"
    logInfo m!"PASS selected52 mean normalization: literal SAME smoothedDefect and revised b squared; no Picard index or extra premise; {axioms}"
end JanetCartan.RevisedUniform.OriginalSelectedMeanNormalization
end
#print axioms JanetCartan.RevisedUniform.OriginalSelectedMeanNormalization.normalizedTarget_eq_smoothedDefect
