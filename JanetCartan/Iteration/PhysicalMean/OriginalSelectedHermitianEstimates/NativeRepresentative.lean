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
# Original full-self prerequisite: NativeRepresentative

The original full sampled self equals the same native-source tensor at the original torus representative.
The public names, original choices and checked proof bodies are retained from
the combined producer. Consumer: the actual `full_self_profile`, and for the
identity leaves the original signed-pair self ledger
(`main:eq:mean-normal-field`, `main:prop:mean`, `main:prop:pairs`).
-/

open scoped BigOperators
/- Actual component: NativeRepresentative. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.NativeRepresentative
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def openApp (e : Expr) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "actual full H: expected original application"
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "actual full H: original body unavailable {name}"
  return ((body.instantiateLevelParams info.levelParams levels).beta e.getAppArgs).headBeta
private meta def binder (label : Name) (domain : Expr) (bi : BinderInfo) : Name :=
  if bi == .instImplicit && domain.isAppOf ``Fintype then `instFintype else label.eraseMacroScopes
private meta def fieldsOf (e : Expr) : MetaM (Array (Name × Expr)) := do
  let info ← getConstInfo e.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams e.getAppFn.constLevels!
  let mut fields := #[]
  for arg in e.getAppArgs do
    let .forallE name dom rest bi := type.consumeMData | throwError "actual full H: original field telescope exhausted"
    fields := fields.push (binder name dom bi,arg)
    type := rest.instantiate1 arg
  return fields
private meta def applyKnown (key : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo key
  let levels := info.levelParams.map (fun _ => Level.zero)
  let mut proof := mkConst key levels
  let mut type := info.type.instantiateLevelParams info.levelParams levels
  for _ in [:64] do
    let .forallE name dom rest bi := type.consumeMData | return proof
    let key := binder name dom bi
    let some (_,arg) := fields.find? (fun kv => kv.1 == key) | throwError "actual full H: missing original field {key}"
    proof := mkApp proof arg
    type := rest.instantiate1 arg
  throwError "actual full H: oversized consumer telescope"
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full H: unresolved original-data declaration {key}"
    unless (e.getUsedConstants.filter fun c => (env.find? c).isNone).isEmpty do
      throwError "actual full H: missing declaration dependency {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual full Hermitian {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual full Hermitian {key}/{p.size}; SAME original sample, μ and full source"
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let x := p[54]!
    let atX := (mkApp f[5]! x).headBeta
    unless atX.isAppOfArity `JanetCartan.CurrentMean.weightedHermitianTensor 9 do throwError "actual full H: full self9 changed"
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    unless Z.isAppOfArity ``HAdd.hAdd 6 do throwError "actual full H: complete B+D sum changed"
    let base := Z.getAppArgs[4]!
    let change := Z.getAppArgs[5]!
    unless change.isAppOfArity ``DFunLike.coe 6 do throwError "actual full H: source linear-map action changed"
    let source := change.getAppArgs[5]!
    let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
    let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
    let hR := app (moment ++ `moment_reached) p[:35].toArray
    let identity := app `JanetCartan.PhysicalPairs.OriginalSourceNative.canonical_derivative_eq_native
      (native ++ #[hγ,hR,p[52]!])
    let prefixProof ← openApp identity
    unless prefixProof.isAppOf `JanetCartan.PhysicalMean.fixedSourceDerivative_eq_individualNativeField do
      throwError "actual full H: original canonical-native proof changed"
    let named ← fieldsOf prefixProof
    let .forallE _ sample _ _ ← inferType a[6]!
      | throwError "actual full H: original weight domain changed"
    let fintype := a[5]!
    unless ← isDefEq (← inferType fintype) (mkApp (mkConst ``Fintype [.zero]) sample) do
      throwError "actual full H: original sample Fintype changed"
    let fields := named ++ #[(`instFintype,fintype),(`μ,a[6]!),(`base,base),(`u,source),(`z,a[8]!)]
    let proof ← applyKnown ``fixedSourceFullHermitian_eq_native fields
    let equality ← inferType proof
    unless equality.isAppOfArity ``Eq 3 do throwError "actual full H: exact tensor identity changed"
    let H := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.fullSampledSelf p[:54].toArray
    let target ← mkEq (mkApp H x) equality.getAppArgs[2]!
    save `full_self_native_representative p[:55].toArray proof target
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.NativeRepresentative
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.full_self_native_representative

