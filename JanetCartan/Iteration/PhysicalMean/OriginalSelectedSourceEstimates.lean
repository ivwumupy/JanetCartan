module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNative
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
meta import Lean
/-!
# Actual selected complete-source native profile

The common D_N is instantiated on the SAME selected full forcing at its original
ONE fixed J=cutoffCount K. The actual native field is globally smooth and has
all physical cNorms bounded by Csource_N(s)*h*R^s. Only the original88 numerical
auxiliary reach is added to the original selected52 data; no analytic source
profile is assumed. Both shells remain in the single complete native field.

This shared producer is consumed by the complete source-amplitude construction
and the original full weighted Hermitian estimate (main:eq:mean-normal-field;
main:prop:mean). Its static Csource is imported from the frozen selected33+N
budget, before the history, target and smoothing parameter. Keep this actual
source leaf frozen when publishing the further Hermitian identities/profiles.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate
private meta def root := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private meta def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private meta def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
private meta def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual native D profile: an additional analytic/source input escaped {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual native D profile: missing original metadata {missing.toList}"
    for old in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "actual native D profile: wrong background-only source"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual complete-source native D profile {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual native D profile: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual native D profile {key}/{p.size}/std3: {axioms}"
run_meta do
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let originalSource := Z.getAppArgs[5]!.getAppArgs[5]!
    let .forallE _ sample _ _ ← inferType a[6]! | throwError "actual native D profile: missing original sample"
    let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
    let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
    let hR90 := app (moment ++ `moment_reached) p[:35].toArray
    let high := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.high_error
      (native ++ #[hγ,hR90])
    let some linear := (← inferType high).find? (·.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear 52)
      | throwError "actual native D profile: no original fixed high-E prefix"
    let L := linear.getAppArgs[51]!
    unless L.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !L.hasLooseBVars do
      throwError "actual native D profile: changed original fixed cutoff"
    if L.containsFVar p[53]!.fvarId! then throwError "actual native D profile: a Picard-dependent cutoff"
    let u := originalSource.replace fun e => if e == p[52]! then some L else none
    forallBoundedTelescope (← inferType high) (some 1) fun reach _ => do
      unless reach.size == 1 do throwError "actual native D profile: wrong numerical auxiliary reach"
      let hAux := reach[0]!
      let N := p[53]!
      let static := p[:33].toArray.push N
      let M := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D static
      let hM := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.D_nonneg static
      let hInitial ← mkAppM ``le_trans
        #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray,native[45]!]
      let facts ← mkAppM ``fixedPicard_history_scale_facts #[hInitial,native[46]!]
      let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
      let hh := part facts 3
      let h := (← inferType hh).getAppArgs[3]!
      withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
        withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
          let stem := app `JanetCartan.PhysicalPairs.OriginalSourceNative.source_cNorm_profile
            (native ++ #[hγ,hR90,L,u,i,s,M,hM,R,h,part facts 0,part facts 2,hh])
          let .forallE _ domain _ _ ← inferType stem
            | throwError "actual native D profile: true Sobolev-source requirement changed"
          let sourceProfile ← forallBoundedTelescope domain (some 2) fun qh _ => do
            unless qh.size == 2 do throwError "actual native D profile: finite all-order source range changed"
            let hp := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.iterate_profile_uniform
              (p[:52].toArray ++ #[hAux,N,N,← mkAppM ``le_refl #[N],qh[0]!])
            let n := mkApp (mkConst ``Nat.succ) native[0]!
            let same := app ``residualSobolevSeminorm_eq_periodicSobolevNorm #[n,qh[0]!,u]
            let converted ← mkAppM ``le_of_eq_of_le #[← mkAppM ``Eq.symm #[same],hp]
            mkLambdaFVars qh converted
          let complete := mkApp stem sourceProfile
          let smooth := Expr.proj ``And 0 complete
          let norms := Expr.proj ``And 1 (Expr.proj ``And 1 complete)
          let proof ← mkAppM ``And.intro #[smooth,norms]
          let raw ← inferType proof
          let some cost := raw.find? (·.isAppOfArity ``nativeIndividualPhysicalProfileConstant 17)
            | throwError "actual native D profile: true-R cost disappeared"
          let target := raw.replace fun e =>
            if e == cost then some (mkApp (app (root ++ `Csource) static) s) else none
          save `native_source_profile (p[:52].toArray ++ #[hAux,N,i,s]) proof target
end JanetCartan.PhysicalMean.OriginalSelectedHermitianProfilesTemplate
#print axioms JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.native_source_profile
