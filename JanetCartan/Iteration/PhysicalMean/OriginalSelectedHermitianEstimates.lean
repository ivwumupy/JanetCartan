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

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.Identities
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.BufferGeometry
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.NativeSourceProfile
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.BaselineProfile

/-!
# Actual full Hermitian estimates on the original normal buffer

Apply the separately checked original baseline, complete native source,
whole-chart identities, unchanged normal buffer and exact total weight to the
SAME selected fullSampledSelf. All prior public names and fixed choices are
preserved. The constant precedes history and target, the Picard run retains
one J = cutoffCount K, and only the original numerical initial reach remains
(`main:eq:mean-normal-field`, `main:prop:mean`).
-/

open scoped BigOperators ContDiff Matrix.Norms.Frobenius
/- Actual component: FullProfile. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.FullProfile
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
/- These four finite input telescopes introduce sample/order/point data and
ordinary propositions only. Keep their literal binder types without the
automatic local-instance scan of `forallBoundedTelescope`: classifying the
fully expanded original buffer membership otherwise exhausts the ordinary
heartbeat budget before the same proof is submitted to the kernel. -/
private meta def forallWithoutInstances {α : Type} (type : Expr) (count : Nat)
    (next : Array Expr → Expr → MetaM α) : MetaM α :=
  go count type #[]
where
  go : Nat → Expr → Array Expr → MetaM α
    | 0, type, params => next params type
    | count + 1, type, params => do
      let .forallE name domain body bi := type.consumeMData
        | throwError "actual full-H profile: the explicit primitive input telescope changed"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        go count (body.instantiate1 x) (params.push x)
private meta def nextDomain (e : Expr) : MetaM Expr := do
  let .forallE _ domain _ _ ← inferType e | throwError "actual full-H profile: consumer field telescope ended"
  return domain
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-H profile: extra analytic input, sample or cutoff escaped {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual full-H profile: missing actual producer {missing.toList}"
    for old in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "actual full-H profile: replaced complete forcing"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual FULL Hermitian profile {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual full-H profile: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual FULL Hermitian profile {key}/{p.size}/std3: {axioms}"
/- Actual application. Every analytic premise is discharged below by a checked
original-data producer. The identical full-H55 application and literal ABI were
checked in the preflight; canonical publication rechecks the same complete proof. -/
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    unless a[0]!.isAppOfArity ``Fin 1 && a[1]!.isAppOfArity ``Fin 1 do
      throwError "actual full-H profile: changed finite physical matrix dimensions"
    let n := a[1]!.appArg!
    let out := a[0]!.appArg!
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual full-H profile: same original sample missing"
    let fintype := a[5]!
    let μ := a[6]!
    let selected := p[:52].toArray
    let fixed := native[:44].toArray
    let static := p[:33].toArray
    let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
    let high := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.high_error
      (native ++ #[app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray,
        app (moment ++ `moment_reached) p[:35].toArray])
    let some linear := (← inferType high).find? (·.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear 52)
      | throwError "actual full-H profile: same fixed high-error cutoff missing"
    let J := linear.getAppArgs[51]!
    unless J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !J.hasLooseBVars do
      throwError "actual full-H profile: not the original fixed J=cutoffCount K"
    forallBoundedTelescope (← inferType high) (some 1) fun reach _ => do
      let hAux := reach[0]!
      let N := p[53]!
      let stage := selected ++ #[J,N]
      let costPrefix := static.push N
      let U := app (root ++ `sourceChart) static
      let hU := app (root ++ `sourceChart_open) static
      let r := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.rBuffer fixed
      let hr := app (root ++ `buffer_pos) static
      let hKU := app (root ++ `buffer_in_source_chart) static
      let B := app (root ++ `sampledBaseline) p[:39].toArray
      let D := app (root ++ `nativeSourceField) stage
      let H := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.fullSampledSelf stage
      let CB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline fixed
      let hCB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline_nonneg fixed
      let CD := app (root ++ `Csource) costPrefix
      let hCD := app (root ++ `Csource_nonneg) costPrefix
      let Cweight := app `JanetCartan.PhysicalMean.OriginalCanonicalWeightMass.Cweight fixed
      let mass := app `JanetCartan.PhysicalMean.OriginalCanonicalWeightMass.selected_weight_mass_le native
      let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift native
      let hμ := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.sample_weights_nonneg (native.push shift)
      let hInitial ← mkAppM ``le_trans
        #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,native[45]!]
      let facts ← mkAppM ``fixedPicard_history_scale_facts #[hInitial,native[46]!]
      let R := (← inferType (part facts 0)).getAppArgs[3]!
      let h := (← inferType (part facts 3)).getAppArgs[3]!
      let sourcePrefix := selected ++ #[hAux,N]
      let baseline (i : Expr) := app (root ++ `sampled_baseline_profile) (p[:39].toArray.push i)
      let source (i q : Expr) := app (root ++ `native_source_profile_on_selected_fields) (sourcePrefix ++ #[i,q])
      let mut proof := mkAppN (mkConst ``OriginalSelectedHermitianProfiles.weighted_full_base_change_profile_on_chart [.zero])
        #[n,out,sample,fintype,r,hr,U,hU,hKU,μ,hμ,B,D]
      let hb ← forallWithoutInstances (← nextDomain proof) 2 fun ih _ =>
        mkLambdaFVars ih (Expr.proj ``And 0 (baseline ih[0]!))
      proof := mkApp proof hb
      let hd ← forallWithoutInstances (← nextDomain proof) 2 fun ih _ =>
        mkLambdaFVars ih (Expr.proj ``And 0 (source ih[0]! (mkNatLit 0)))
      proof := mkAppN proof #[hd,CB,CD,hCB,hCD,R,h,Cweight,part facts 0,part facts 4,mass]
      withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
        let mut proof := mkApp proof s
        let bp ← forallWithoutInstances (← nextDomain proof) 6 fun args _ => do
          let onChart := mkAppN hKU #[args[4]!,args[5]!]
          let jet := mkAppN (Expr.proj ``And 1 (baseline args[0]!)) #[args[2]!,args[4]!,onChart]
          mkLambdaFVars args jet
        proof := mkApp proof bp
        let dp ← forallWithoutInstances (← nextDomain proof) 4 fun args target => do
          let lhs := target.getAppArgs[2]!
          unless lhs.isAppOfArity ``JanetCartan.cNorm 9 do
            throwError "actual full-H profile: physical source cNorm9 changed"
          let K := lhs.getAppArgs[6]!
          let bound := mkApp (Expr.proj ``And 1 (source args[0]! args[2]!)) K
          mkLambdaFVars args bound
        let bound := mkApp proof dp
        let heq := app (root ++ `full_self_native_on_chart) stage
        let normEq := mkAppN (mkConst ``OriginalSelectedHermitianProfiles.full_self_cNorm_eq_native_on_chart [.zero])
          #[n,out,sample,fintype,U,hU,r,hKU,μ,B,D,H,heq,s]
        let complete ← mkAppM ``le_of_eq_of_le #[normEq,bound]
        let raw ← inferType complete
        let rhs := raw.getAppArgs[3]!
        unless rhs.isAppOfArity ``HMul.hMul 6 do
          throwError "actual full-H profile: physical R-power factorization changed"
        let cost := rhs.getAppArgs[4]!
        let expected := raw.replace fun e =>
          if e == cost then some (mkApp (app (root ++ `CH) costPrefix) s) else none
        save `full_self_profile (selected ++ #[hAux,N,s]) complete expected
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate.FullProfile
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.full_self_profile
