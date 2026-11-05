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


/-!
# Original full-self prerequisite: SelectedFields

Names for the same original baseline, complete native source and whole source chart; no new selection.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: SelectedFields. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SelectedFields
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "actual chart H: expected original application"
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "actual chart H: unavailable {name}"
  return ((body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private meta def termWith (vars : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code)
private meta def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual chart H: nonstatic/unresolved declaration {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking exact full-chart H {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual chart H: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS exact full-chart H {key}/{p.size}/std3: {axioms}"
elab "retain_actual_full_hermitian_chart " mode:num : command => liftTermElabM do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let x := p[54]!
    let atX := (mkApp f[5]! x).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let base := Z.getAppArgs[4]!
    let source := Z.getAppArgs[5]!.getAppArgs[5]!
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual chart H: missing original sample type"
    withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
      if mode.getNat == 0 then
        let β ← termWith [(`base,base),(`x,x),(`i,i)] "base.val (JanetCartan.torusQuotient x) i"
        let B ← mkLambdaFVars #[i,x] β
        save `sampledBaseline p[:39].toArray B (← inferType B) true
      else if mode.getNat == 1 then
        let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
        let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
        let hR := app (moment ++ `moment_reached) p[:35].toArray
        let mut equality ← openApp (app `JanetCartan.PhysicalPairs.OriginalSourceNative.identity_statement
          (native ++ #[hγ,hR,p[52]!]))
        for v in #[source,a[8]!,i] do
          let .forallE _ _ body _ := equality | throwError "actual chart H: changed native identity telescope"
          equality := body.instantiate1 v
        unless equality.isAppOfArity ``Eq 3 do throwError "actual chart H: native identity changed"
        let rawD := equality.getAppArgs[2]!
        unless rawD.isAppOfArity ``individualNativeInverseField 10 do throwError "actual chart H: incomplete native D"
        let D ← mkLambdaFVars #[i] rawD.appFn!
        save `nativeSourceField p[:54].toArray D (← inferType D) true
      else
        let angular := app `JanetCartan.PhysicalPairs.OriginalSourceAmplitude.angular_on_original_statement
          (native ++ #[p[52]!,source,i])
        let chart ← forallBoundedTelescope (← openApp angular) (some 2) fun xh _ => do
          let mem ← inferType xh[1]!
          unless mem.isAppOfArity ``Membership.mem 5 do throwError "actual chart H: no original chart membership"
          let chart := mem.getAppArgs[3]!
          unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
            throwError "actual chart H: not the original full SourceMasks.chart23"
          return chart
        if mode.getNat == 2 then
          save `sourceChart p[:33].toArray chart (← inferType chart) true
        else
          let U := app (root ++ `sourceChart) p[:33].toArray
          if mode.getNat == 3 then
            let hopen := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs
            let openType ← mkAppM ``IsOpen #[U]
            save `sourceChart_open p[:33].toArray hopen openType

end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.SelectedFields
retain_actual_full_hermitian_chart 0
retain_actual_full_hermitian_chart 1
retain_actual_full_hermitian_chart 2
retain_actual_full_hermitian_chart 3

#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sampledBaseline
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.nativeSourceField
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sourceChart
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sourceChart_open

