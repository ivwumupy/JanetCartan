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
# Original full-self prerequisite: BufferGeometry

The original 11a/12 normal buffer lies in the same whole source chart; the physical cutoff is unchanged.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
open scoped ContDiff Matrix.Norms.Frobenius
/- Actual component: BufferGeometry. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.BufferGeometry
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "actual H buffer: expected original application"
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "actual H buffer: unavailable {name}"
  return ((body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual H buffer: later data/unresolved input escaped {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual H buffer: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual 11a/12 buffer {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual H buffer: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual 11a/12 buffer {key}/{p.size}/std3: {axioms}"
elab "prove_actual_full_hermitian_buffer " mode:num : command => liftTermElabM do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let source := Z.getAppArgs[5]!.getAppArgs[5]!
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual H buffer: missing original sample type"
    withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
      let angular := app `JanetCartan.PhysicalPairs.OriginalSourceAmplitude.angular_on_original_statement
        (native ++ #[p[52]!,source,i])
      forallBoundedTelescope (← openApp angular) (some 2) fun xy _ => do
        let mem ← inferType xy[1]!
        unless mem.isAppOfArity ``Membership.mem 5 do throwError "actual H buffer: source chart membership changed"
        let U := mem.getAppArgs[3]!
        unless U.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
          throwError "actual H buffer: not the whole original source chart23"
        let chi := app `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂ U.getAppArgs
        let hs := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_support_chart U.getAppArgs
        let fixed := native[:44].toArray
        let radius := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.rBuffer fixed
        let geometry := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.radius_geometry fixed
        if mode.getNat == 0 then
          let hr := Expr.proj ``And 0 geometry
          save `buffer_pos p[:33].toArray hr (← inferType hr)
        else
          let inside := Expr.proj ``And 0 (Expr.proj ``And 1 geometry)
          let hrIn ← mkAppM ``le_of_lt #[inside]
          let n := mkApp (mkConst ``Nat.succ) U.getAppArgs[0]!
          let proof := app ``OriginalSelectedHermitianProfiles.original_buffer_subset_source_chart
            #[n,chi,U,hs,radius,hrIn]
          save `buffer_in_source_chart p[:33].toArray proof (← inferType proof)
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.BufferGeometry
prove_actual_full_hermitian_buffer 0
prove_actual_full_hermitian_buffer 1
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.buffer_pos
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.buffer_in_source_chart

