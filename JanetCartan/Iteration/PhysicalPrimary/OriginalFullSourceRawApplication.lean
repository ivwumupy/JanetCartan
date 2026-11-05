module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawSourceProfile
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawSourceProfile
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
/-!
# Actual full-forcing source in the before-response raw derivative field

The exact consumer is `OriginalRawSourceProfile.source_cNorm_profile` in
`main:eq:primary-strain`. Its source profile through s+n+2 is supplied by
COMMON D_N, not P_N or the scalar Fourier mass. The original inverse, measured
adjoint, mask, phase, sample and fixed J remain unchanged; only the already
proved before-B output amplitude occurs. This does not assert the separate
raw derivative factorization, baseline profile, or first-mask strain decay.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullSourceRawApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile
private def picard := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
private def save (key : Name) (p : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw full source: later input or analytic premise escaped {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual raw full source: missing original metadata {missing.toList}"
    for old in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then throwError "actual raw full source: background-only forcing escaped"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual raw full-source {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME before-B raw derivative source field at the genuine full-forcing Picard run and ONE fixed J. Its true-R physical jets use common D_N through s+n+2, with static selected33+N cost before history/target/smoothing; only the numerical initial auxiliary reach remains. No corrected-G identification, scalar-mass substitute or analytic success premise (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual raw full source: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual raw full-source {key}/{p.size}: {axioms}"

structure Input where
  native : Array Expr
  selected : Array Expr
  hAux : Expr
  N : Expr
  i : Expr
  s : Expr
  field : Expr
  proof : Expr
  target : Expr
  cost : Expr
  hM : Expr

def Input.fixed (d : Input) := d.selected[:33].toArray.push d.N
def Input.fieldArgs (d : Input) := d.selected ++ #[d.N,d.i]
def Input.profileArgs (d : Input) := d.selected ++ #[d.hAux,d.N,d.i,d.s]

/-- One literal original source application; no analytic field is supplied by a caller. -/
def withActual (next : Input → MetaM Unit) : MetaM Unit :=
  PhysicalMean.OriginalFullSourcePicard.withFullData fun native selected point high J => do
    unless native.size == 50 && selected.size == 52 && point.size == 47 do
      throwError "actual raw source: native/selected admission boundary changed"
    forallBoundedTelescope (← inferType high) (some 1) fun numeric _ => do
      unless numeric.size == 1 do throwError "actual raw source: initial auxiliary reach changed"
      withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
        let full := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource selected
        let u := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing
          (native ++ #[J,full,N])
        let pre := native ++ #[point[27]!,point[39]!,J,u]
        let unindexed := app (raw ++ `field) pre
        forallBoundedTelescope (← inferType unindexed) (some 1) fun sample _ => do
          unless sample.size == 1 do throwError "actual raw source: original sample boundary changed"
          let params := pre ++ sample
          let static := selected[:33].toArray.push N
          let M := app (picard ++ `D) static
          let hM := app (picard ++ `D_nonneg) static
          let hInitial ← mkAppM ``le_trans
            #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray,native[45]!]
          let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
          let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
          let hh := part facts 3
          let h := (← inferType hh).getAppArgs[3]!
          withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
            let all := params ++ #[s,M,hM,R,h,part facts 0,part facts 2,hh]
            let stem := app (raw ++ `source_cNorm_profile) all
            let .forallE _ sourceRequirement _ _ ← inferType stem
              | throwError "actual raw source: source-profile requirement changed"
            let sourceProof ← forallBoundedTelescope sourceRequirement (some 2) fun qh _ => do
              unless qh.size == 2 do throwError "actual raw source: finite source range changed"
              let hp := app (picard ++ `iterate_profile_uniform)
                (selected ++ #[numeric[0]!,N,N,← mkAppM ``le_refl #[N],qh[0]!])
              let n := mkApp (mkConst ``Nat.succ) native[0]!
              let same := app `JanetCartan.PhysicalMean.residualSobolevSeminorm_eq_periodicSobolevNorm #[n,qh[0]!,u]
              let converted ← mkAppM ``le_of_eq_of_le #[← mkAppM ``Eq.symm #[same],hp]
              mkLambdaFVars qh converted
            let proof := mkApp stem sourceProof
            let info ← getConstInfo (raw ++ `profile_statement)
            let target := ((info.value! (allowOpaque := true)).beta (all.push sourceProof)).headBeta
            let some cost := target.find? (·.isAppOfArity `JanetCartan.PhysicalMean.nativeIndividualPhysicalProfileConstant 17)
              | throwError "actual raw source: genuine before-B cost disappeared"
            let ca := cost.getAppArgs
            unless ca[7]!.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCostTotal 44 &&
                ca[11]! == M do
              throwError "actual raw source: corrected output budget or scalar mass replaced the common source budget"
            let closed ← mkLambdaFVars (static.push s) cost
            if closed.hasFVar || closed.hasLooseBVars then throwError "actual raw source: cost varies with later inputs"
            next {
              native := native
              selected := selected
              hAux := numeric[0]!
              N := N
              i := sample[0]!
              s := s
              field := app (raw ++ `field) params
              proof := proof
              target := target
              cost := cost
              hM := hM }

elab "publish_actual_full_source_raw " mode:num : command => liftTermElabM do
  unless mode.getNat < 4 do throwError "actual raw full source: unknown mode"
  withActual fun d => do
    if mode.getNat == 0 then
      let value ← mkLambdaFVars #[d.s] d.cost
      save `Csource d.fixed value (← inferType value) true
    else if mode.getNat == 1 then
      let a := d.cost.getAppArgs
      let hCinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv_nonneg d.native[:44].toArray
      let proof := app `JanetCartan.PhysicalMean.nativeIndividualPhysicalProfileConstant_nonneg
        (a[:15].toArray ++ #[hCinv,d.hM] ++ a[15:].toArray)
      let target := (← inferType proof).replace fun e =>
        if e == d.cost then some (mkApp (app (root ++ `Csource) d.fixed) d.s) else none
      save `Csource_nonneg d.fixed (← mkLambdaFVars #[d.s] proof) (← mkForallFVars #[d.s] target)
    else if mode.getNat == 2 then
      save `field d.fieldArgs d.field (← inferType d.field) true
    else
      let named := app (root ++ `field) d.fieldArgs
      let namedCost := mkApp (app (root ++ `Csource) d.fixed) d.s
      let target := d.target.replace fun e =>
        if e == d.field then some named else if e == d.cost then some namedCost else none
      unless (target.find? (· == named)).isSome && (target.find? (· == namedCost)).isSome do
        throwError "actual raw full source: named field or prehistory cost disappeared"
      save `source_profile d.profileArgs d.proof target
end JanetCartan.PhysicalPrimary.OriginalFullSourceRawApplication
end
