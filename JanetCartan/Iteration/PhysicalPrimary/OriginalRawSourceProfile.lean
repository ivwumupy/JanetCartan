module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawForwardSlice
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNative
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! # True R-scale profiles of the actual before-B native raw source field

The raw forward matrix and ALL its smoothness/support/jet certificates are
independently constructed from raw13. The source inverse, measured adjoint,
relative phase, native mask and half-moment normalization are unchanged.
The only analytic data left here are the genuine source Sobolev profile through
s+n+2; its actual producer is the common D_N profile of the full forcing run.
This leaf does not identify corrected G with raw G or assert first-mask decay.
Consumer: the original full χ2 half-stress source for main:eq:primary-strain.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalRawSourceProfileApplication
open Lean Meta Elab Command
open PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward
private def old := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def put (fields : Array (Name × Expr)) (key : Name) (value : Expr) :=
  (fields.filter (fun p => p.1 != key)).push (key,value)
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw source profile: unresolved field {key}"
  let name := ns ++ key
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let out ← liftM IO.getStdout
  liftM <| out.putStrLn s!"actual raw source profile: checking {key}/{p.size}"
  liftM <| out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The independently constructed before-B native raw source field of the SAME unweighted adjoint and current inverse has true R-scale profiles. Source Sobolev data through s+n+2 remain explicit for actualization by the common D_N profile, not a corrected-G identification (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  logInfo m!"actual raw source profile: checked {key}/{p.size}"

/-- Only raw certificates replace their previously corrected analogues; the
saved sampled shape is retained so no large kernel reduction is repeated by
later currying. -/
private def rawSubstitute (e : Expr) : Expr :=
  let substitutions := #[(old ++ `forwardAmplitude,raw ++ `forwardAmplitude),
    (old ++ `forwardAmplitude_contDiff,raw ++ `forwardSmooth),
    (old ++ `forwardAmplitude_tsupport,raw ++ `forwardSupport),
    (old ++ `forwardAmplitude_total_jets,raw ++ `forwardTotalJets),
    (old ++ `forwardAmplitudeBudgetTotal,raw ++ `forwardCostTotal),
    (old ++ `Sampled.amp,ns ++ `Sampled.amp),
    (`JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles.cutAmplitude,raw ++ `cutAmplitude)]
  e.replace fun e =>
    if let some (_,target) := substitutions.find? (fun entry => e.isAppOf entry.1) then
      some (mkAppN (mkConst target e.getAppFn.constLevels!) e.getAppArgs)
    else none

elab "check_actual_raw_source_primitive " field:ident : command => liftTermElabM do
  let key := field.getId.eraseMacroScopes
  unless #[`amp,`hamp,`hampK,`hGj].contains key do
    throwError "actual raw source primitive: unknown independent certificate"
  let info ← getConstInfo (old ++ `Sampled ++ key)
  let some value := info.value? (allowOpaque := true) |
    throwError "actual raw source primitive: original saved body unavailable"
  forallBoundedTelescope info.type (some 53) fun p target => do
    unless p.size == 53 do throwError "actual raw source primitive: original53 changed"
    let value := rawSubstitute (value.beta p).headBeta
    let target := rawSubstitute target
    unless (value.find? (fun e => e.isConstOf (raw ++ `forwardAmplitude) ||
        e.isConstOf (raw ++ `forwardSmooth) || e.isConstOf (raw ++ `forwardSupport) ||
        e.isConstOf (raw ++ `forwardTotalJets))).isSome do
      throwError "actual raw source primitive: independent raw certificate absent"
    save (`Sampled ++ key) p value target (key == `amp)

/-- Change only the forward fields to their separately checked RAW producers.
The measured operator An, its original-moment witness, phase, mask and Q0 stay
literal. The corrected G identity is intentionally absent. -/
private def withRawFields (p : Array Expr) (fields : Array (Name × Expr)) : MetaM (Array (Name × Expr)) := do
  let mut result := fields.filter (fun e => e.1 != `G && e.1 != `hG)
  for key in #[`amp,`hamp,`hampK,`hGj] do
    let original ← getField fields key
    unless original.isAppOfArity (old ++ `Sampled ++ key) 53 do
      throwError "actual raw source profile: saved sampled53 certificate changed"
    result := put result key (app (ns ++ `Sampled ++ key) original.getAppArgs)
  result := put result `aG (app (raw ++ `forwardCostTotal) p[:44].toArray)
  result := put result `haG (app (raw ++ `forwardCostTotal_nonneg) p[:44].toArray)
  return result

partial def publish (params : Array Expr) (original : Array (Name × Expr)) (mode : Nat) : MetaM Unit := do
  unless params.size == 53 && mode < 3 do throwError "actual raw source profile: native ABI changed"
  let common ← withInverseBudget params (← withRawFields params original)
  let fixed ← budgetPrefix params common
  let n ← getField common `n
  let ν ← getField common `ν
  let residualType ← mkAppM ``CoeSort.coe #[app `JanetCartan.CurrentMean.SmoothResidual #[n]]
  withLocalDeclD `u residualType fun u => do
    withLocalDeclD `i ν fun i => do
      let e ← mkAppM ``DFunLike.coe #[app `JanetCartan.CurrentMean.smoothResidualToL2 #[n],u]
      let mut known := common ++ #[(`u,u),(`e,e)]
      for (key,source) in #[(`A,`An),(`hA,`hAn),(`Tbare,`Tbare),(`hTbare,`hTbare),(`hTbareBound,`hTbareBound)] do
        known := put known key (mkApp (← getField common source) i)
      let conversions : Array (Name × String) := #[
        (`φ,"(fun z => φ ((i,z.1),z.2))"),(`m,"(fun z => m ((i,z.1),z.2))"),
        (`G,"(fun a c j => amp a c (i,j))"),(`hGK,"(fun a c j η => hampK a c (i,j) η)"),
        (`Φ,"(fun j => Φ (i,j))"),(`a,"(fun a j => ameas a (i,j))"),(`L,"(fun j => L (i,j))"),
        (`hφs,"(fun z => hφs ((i,z.1),z.2))"),(`hΦ,"(fun j => hΦ (i,j))"),
        (`hG,"(fun a c j => hamp a c (i,j))"),(`ha,"(fun a j => ha a (i,j))"),
        (`hL,"(fun j v => hL (i,j) v)"),(`hhigh,"(fun z => hhigh ((i,z.1),z.2))"),
        (`haK,"(fun a j η => haK a (i,j) η)"),(`hagree,"(fun z => hagree ((i,z.1),z.2))"),
        (`hphase,"(fun z => hphase ((i,z.1),z.2))"),(`hGj,"(fun a c j η => hGj a c (i,j) η)"),
        (`hΦj,"(fun j η => hΦj (i,j) η)"),(`haj,"(fun a j η => haj a (i,j) η)"),
        (`hLj,"(fun j η => hLj (i,j) η)")]
      let helpers := #[(`hφ,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_phase),
        (`hm,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_mask),
        (`hms,`JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.curried_original_mask_compact)]
      let allowed := #[`s,`M,`hM,`R,`h,`hR,`hTR,`hh,`hsource]
      let consumer := `JanetCartan.PhysicalMean.individualNativeInverseField_cNorm_source_profile
      let info ← getConstInfo consumer
      let levels := info.levelParams.map (fun _ => Level.zero)
      let literal := mkConst consumer levels
      let rec go (type : Expr) (args : Array Expr) (known : Array (Name × Expr))
          (bound : Array Expr) : MetaM Unit := do
        match type with
        | .forallE binder domain body bi =>
          let field := binderKey binder domain bi
          if field == `hreg || field == `hinverse then
            let all ← sourceTail params known (field == `hreg)
            let proof ← if field == `hreg then pure all else
              forallBoundedTelescope domain (some 2) fun xs _ => do
                unless xs.size == 2 do throwError "actual raw source: inverse finite-order boundary changed"
                mkLambdaFVars xs (mkApp all xs[0]!)
            go (body.instantiate1 proof) (args.push proof) (put known field proof) bound
          else if allowed.contains field then
            if known.any (fun entry => entry.1 == field) then
              throwError "actual raw source: analytic input incorrectly provided by metadata {field}"
            withLocalDeclNoLocalInstanceUpdate binder bi domain fun x =>
              go (body.instantiate1 x) (args.push x) (known.push (field,x)) (bound.push x)
          else
            let value ← match conversions.find? (fun entry => entry.1 == field) with
              | some (_,code) => termWith ((`i,i) :: common.toList) code (some domain)
              | none => match helpers.find? (fun entry => entry.1 == field) with
                | some (_,helper) => applyFields helper (common.push (`i,i))
                | none => getField known field
            go (body.instantiate1 value) (args.push value) (put known field value) bound
        | target =>
          let some cost := target.find? (·.isAppOf `JanetCartan.PhysicalMean.nativeIndividualPhysicalProfileConstant) |
            throwError "actual raw source: missing true R-scale profile constant"
          let M ← getField known `M
          let s ← getField known `s
          let closed ← mkLambdaFVars (fixed ++ #[M,s]) cost
          if closed.hasFVar || closed.hasLooseBVars then
            throwError "actual raw source: scale/history/prefix/sample/source entered static constant"
          let some field := target.find? (·.isAppOf `JanetCartan.PhysicalMean.individualNativeInverseField) |
            throwError "actual raw source: missing raw native field"
          unless (field.find? (·.isConstOf (ns ++ `Sampled.amp))).isSome do
            throwError "actual raw source: exact independently constructed raw amplitude absent"
          if mode == 0 then save `field (params ++ #[u,i]) field (← inferType field) true
          else
            let target := target.replace fun e => if e == field then some (app (ns ++ `field) (params ++ #[u,i])) else none
            let all := params ++ #[u,i] ++ bound
            if mode == 1 then save `profile_statement all target (mkSort .zero) true
            else save `source_cNorm_profile all (mkAppN literal args) (app (ns ++ `profile_statement) all)
      go (info.type.instantiateLevelParams info.levelParams levels) #[] known #[]

check_actual_raw_source_primitive amp
check_actual_raw_source_primitive hamp
check_actual_raw_source_primitive hampK
check_actual_raw_source_primitive hGj
run_elab do
  PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => publish p fields 0
run_elab do
  PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => publish p fields 1
run_elab do
  PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => publish p fields 2
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.field
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.profile_statement
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.source_cNorm_profile
end JanetCartan.PhysicalPrimary.OriginalRawSourceProfileApplication
end
