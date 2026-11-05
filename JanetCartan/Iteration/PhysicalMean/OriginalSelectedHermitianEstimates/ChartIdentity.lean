module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceChartRepresentative
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalWeightMass
public meta import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
meta import Lean
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNodeNative
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaselineApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedSourceEstimates
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.RepresentativeTransport
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.NativeRepresentative
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.SelectedFields

/-!
# Original full-self prerequisite: ChartIdentity

Remove the torus representative on the whole original source chart for the same full self.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: WholeChartIdentity. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.WholeChartIdentity.ChartIdentity
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "whole-chart H: original application expected"
  let ci ← getConstInfo name
  let some value := ci.value? (allowOpaque := true) | throwError "whole-chart H: original body unavailable"
  return ((value.instantiateLevelParams ci.levelParams levels).beta e.getAppArgs).headBeta
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "whole-chart full-H identity: unresolved original input {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "whole-chart full-H identity: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking exact whole-chart H {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "whole-chart H: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS exact whole-chart H {key}/{p.size}/std3: {axioms}"
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f _ _ _ => do
    let x := p[54]!
    let atX := (mkApp f[5]! x).headBeta
    let a := atX.getAppArgs
    unless a[0]!.isAppOfArity ``Fin 1 && a[1]!.isAppOfArity ``Fin 1 do
      throwError "whole-chart H: original finite matrix dimensions changed"
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "whole-chart H: original sample missing"
    let U ← openApp (app (root ++ `sourceChart) p[:33].toArray)
    unless U.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
      throwError "whole-chart H: original whole source chart changed"
    withLocalDeclNoLocalInstanceUpdate `hx .default (← mkAppM ``Membership.mem #[U,x]) fun hx => do
      let rep := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.representative_on_original_chart
        (U.getAppArgs ++ #[x,hx])
      let y := (← inferType rep).getAppArgs[1]!
      let B := app (root ++ `sampledBaseline) p[:39].toArray
      let D := app (root ++ `nativeSourceField) p[:54].toArray
      let H := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.fullSampledSelf p[:54].toArray
      let he := app (root ++ `full_self_native_representative) p[:55].toArray
      let proof := mkAppN (mkConst ``OriginalSelectedHermitianProfiles.weighted_full_self_remove_representative [.zero])
        #[a[1]!.appArg!,a[0]!.appArg!,sample,a[5]!,a[6]!,B,D,x,y,rep,mkApp H x,he]
      save `full_self_native_on_chart (p[:55].toArray.push hx) proof (← inferType proof)
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.WholeChartIdentity.ChartIdentity
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.weighted_full_self_remove_representative
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.full_self_native_on_chart

