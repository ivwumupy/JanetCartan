module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawSourceProfile
public import JanetCartan.Iteration.PhysicalMean.GroupedCurrent
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public meta import Lean
/-!
# The full original raw annular sum is the same native raw source field

Consumer: the actual before-B raw source reconstruction for
`main:eq:primary-strain` and `app:ch_waves:thm:individual`. The whole annular sum
uses the original real adjoint, complex measured operator, current inverse,
source, phase, already-prefixed mask, half-moment and annular measure. Only the
output amplitude and its certificates are the independently constructed RAW
ones. No corrected periodic derivative family is identified with a raw family.

The generic grouped-current identity needs the real/complex representation
`hArep`, not the measured-operator certificate named `hAn` in the shared tuple.
The original source and every refined annulus are retained before any norm,
cutoff estimate, strain operation or first-mask source profile is considered.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization
open Lean Meta
open JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
  (getField binderKey applyFields)
private def root := `JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile
private def old := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def put (fields : Array (Name × Expr)) (key : Name) (value : Expr) :=
  (fields.filter (fun p => p.1 != key)).push (key,value)
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Elab.Term.TermElabM.run' (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def openApp (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) | throwError "raw grouped: unavailable {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta
private def withRaw (p : Array Expr) (original : Array (Name × Expr)) : MetaM (Array (Name × Expr)) := do
  let mut fields := original.filter (fun e => e.1 != `G && e.1 != `hG)
  for key in #[`amp,`hamp,`hampK] do
    let value ← getField original key
    unless value.isAppOfArity (old ++ `Sampled ++ key) 53 && value.getAppArgs == p do
      throwError "raw grouped: changed actual sampled53 {key}"
    fields := put fields key (app (raw ++ `Sampled ++ key) p)
  return fields
private def groupedPrefix (fields : Array (Name × Expr)) : MetaM Expr := do
  let key := `JanetCartan.PhysicalMean.groupedOriginalCurrentField_eq_individualNativeInverseField
  let ci ← getConstInfo key
  let levels := ci.levelParams.map (fun _ => Level.zero)
  let mut proof := mkConst key levels
  let mut type := ci.type.instantiateLevelParams ci.levelParams levels
  let conversions : Array (Name × String) := #[
    (`φ,"(fun i z => φ ((i,z.1),z.2))"),
    (`m,"(fun i z => m ((i,z.1),z.2))"),
    (`G,"(fun i a c j => amp a c (i,j))"),
    (`hGK,"(fun i a c j η => hampK a c (i,j) η)")]
  let helpers : Array (Name × Name) := #[
    (`hφ,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_phase),
    (`hm,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_mask),
    (`hms,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_mask_compact),
    (`hGc,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_amplitude)]
  while type.isForall do
    let .forallE binder domain rest bi := type | throwError "raw grouped: changed generic telescope"
    let name := binderKey binder domain bi
    if name == `u then return proof
    let value ← if name == `hAn then getField fields `hArep else
      match helpers.find? (fun e => e.1 == name) with
      | some (_,helper) => applyFields helper fields (some `i)
      | none => match conversions.find? (fun e => e.1 == name) with
        | some (_,code) => termWith fields.toList code (some domain)
        | none => getField fields name
    proof := mkApp proof value
    type := rest.instantiate1 value
  throwError "raw grouped: generic consumer lost the original source input"
private def exposeSum (lhs : Expr) : MetaM Expr := do
  unless lhs.isAppOf `JanetCartan.PhysicalMean.groupedAnnularForwardField do
    throwError "raw grouped: not the FULL grouped field"
  let exposed ← openApp lhs
  let annular ← getConstInfo `JanetCartan.PhysicalMean.annularForwardField
  let some value := annular.value? (allowOpaque := true) | throwError "raw grouped: missing annular body"
  let result := exposed.replace fun e =>
    if e.isAppOf annular.name then
      some (((value.instantiateLevelParams annular.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta)
    else none
  unless result.isAppOf ``Finset.sum &&
      (result.find? (·.isAppOf ``MeasureTheory.integral)).isSome &&
      (result.find? (·.isAppOf `JanetCartan.PhysicalForwardMean.physicalForwardKernel)).isSome do
    throwError "raw grouped: exposure lost exact full annular sum/integral/kernel"
  if (result.find? (fun e => e.isAppOf `JanetCartan.PhysicalMean.groupedAnnularForwardField ||
      e.isAppOf annular.name)).isSome then throwError "raw grouped: grouped/annular head remains"
  return result
private def save (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw grouped: unresolved actual declaration"
    unless (e.getUsedConstants.filter fun n => (env.find? n).isNone).isEmpty do
      throwError "raw grouped: missing actual constant"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ `raw_annular_sum_eq_field
  IO.println s!"Kernel checking SAME full raw annular realization/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "For the SAME original primitive53, smooth source, sample and physical point, the literal WHOLE RAW angular annular sum equals the unchanged native raw source field55. Original real adjoint, complex measured An, Q0, phase, mask, sqrtNorm half-moment and measure are retained; only raw output amp/hamp/hampK are substituted. Uses common hArep in the generic hAn slot, with no corrected-G identification or additional analytic premise (main:eq:primary-strain; app:ch_waves:thm:individual)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "raw grouped: nonstandard axioms {ax}"
  logInfo m!"PASS actual full raw annular realization/{p.size}/std3: {ax}"
run_meta do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p original => do
    unless p.size == 53 do throwError "raw grouped: primitive53 changed"
    let fields ← withRaw p original
    let h ← groupedPrefix fields
    let n ← getField fields `n
    let ν ← getField fields `ν
    let residual ← mkAppM ``CoeSort.coe #[app `JanetCartan.CurrentMean.SmoothResidual #[n]]
    withLocalDeclD `u residual fun u => do
      withLocalDeclD `i ν fun i => do
        withLocalDeclD `x (app `JanetCartan.Euclidean #[n]) fun x => do
          let source ← mkAppM ``DFunLike.coe #[app `JanetCartan.CurrentMean.smoothResidualToL2 #[n],u]
          let point ← mkCongrFun (mkAppN h #[source,i]) x
          let eq ← inferType point
          unless eq.isAppOfArity ``Eq 3 do throwError "raw grouped: not a pointwise equality"
          let lhs ← exposeSum eq.getAppArgs[1]!
          let rhs := mkApp (app (raw ++ `field) (p ++ #[u,i])) x
          unless (lhs.find? (·.isAppOf (raw ++ `Sampled.amp))).isSome do
            throwError "raw grouped: raw output amplitude absent"
          for key in #[`φ,`m] do
            unless (lhs.find? (·.isAppOf (old ++ `Sampled ++ key))).isSome do
              throwError "raw grouped: original phase/mask lost {key}"
          logInfo "SAME original A/An/Q0/phase/mask/source/sqrtNorm/annular measure, raw output only; hAn uses hArep"
          save (p ++ #[u,i,x]) point (← mkEq lhs rhs)
#print axioms JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization.raw_annular_sum_eq_field
end JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization
end
