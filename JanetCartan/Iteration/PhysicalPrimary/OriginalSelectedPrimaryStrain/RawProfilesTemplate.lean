module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawBaselineProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourceRawProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeProfilesTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual before-response amplitude profiles for the primary strain

The consumer is the first-mask source in `main:eq:primary-strain`. The raw
amplitude is the unscaled raw baseline plus the original raw forward field of
the complete-forcing Picard iterate. Both existing profile producers are used
on the same outer sample and whole source chart. The coefficient precedes the
history, target and smoothing order, after the fixed finite Picard count only.
This file does not identify this amplitude with a raw wave derivative; that
independent identity belongs to `Factorization`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfilesTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles
private def raw := `JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles
private def baseline := `JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
private def termWith (bindings : List (Name × Expr)) (text : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text goal)

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "actual primary raw profile: unresolved or late operand in {key}"
    unless (e.getUsedConstants.filter fun n => (env.find? n).isNone).isEmpty do
      throwError "actual primary raw profile: missing original private metadata in {key}"
    for old in #[source ++ `iterate,source ++ `selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then
        throwError "actual primary raw profile: background-only source escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual primary raw profile {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The original unscaled RAW baseline plus the SAME complete-forcing Picard raw source has true R-scale jets on the whole original source chart. Both analytic profile producers are applied; the fixed selected33+N price precedes every history, target and smoothing parameter (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary raw profile: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual primary raw profile {key}/{p.size}: {axioms}"

structure Data where
  native : Array Expr
  selected : Array Expr
  hAux : Expr
  steps : Expr
  sample : Expr
  sourceArgs : Array Expr
  baselineArgs : Array Expr
  baseline : Expr
  source : Expr
  hBaseline : Expr

def Data.fixed (d : Data) := d.selected[:33].toArray.push d.steps
def Data.args (d : Data) := d.selected ++ #[d.steps,d.sample]
def Data.profileArgs (d : Data) := d.selected ++ #[d.hAux,d.steps,d.sample]

private def profileTelescope (count : Nat) (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,type,p => next p (type.instantiateRev p)
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual primary raw profile: published telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

/-- Read the SAME original selected source from its published raw-profile
interface. The original outer baseline operands are recovered from their
existing exact identity; no corrected derivative bound is used. -/
def withData (next : Data → MetaM Unit) : MetaM Unit := do
  profileTelescope 55 (← getConstInfo (raw ++ `source_profile)).type fun p rest => do
    unless rest.isForall do throwError "actual primary raw profile: source jet order disappeared"
    let selected := p[:52].toArray
    let fieldArgs := selected ++ #[p[53]!,p[54]!]
    let sourceField := app (raw ++ `field) fieldArgs
    let ci ← getConstInfo (raw ++ `field)
    let original := ((ci.value! (allowOpaque := true)).beta fieldArgs).headBeta
    unless original.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile.field 55 do
      throwError "actual primary raw profile: original raw source55 changed"
    let actual := original.getAppArgs
    let sourceArgs := actual[:50].toArray ++ actual[52:].toArray
    let eq ← inferType (app
      `JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentity.baseline_eq_actual_baseline sourceArgs)
    unless eq.isAppOfArity ``Eq 3 && eq.getAppArgs[2]!.isAppOfArity
        `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.baselineAmplitude 56 do
      throwError "actual primary raw profile: original outer56 baseline changed"
    let baseArgs := eq.getAppArgs[2]!.getAppArgs
    let iType ← inferType p[54]!
    unless iType.isAppOfArity ``JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual primary raw profile: original finite sample changed"
    let hi := mkAppN (mkConst
      `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.original_sample_weight_ne_zero [.zero])
      (iType.getAppArgs.push p[54]!)
    next {
      native := actual[:50].toArray,selected := selected,hAux := p[52]!,steps := p[53]!,sample := p[54]!,
      sourceArgs := sourceArgs,baselineArgs := baseArgs,
      baseline := app (baseline ++ `baseline) baseArgs,source := sourceField,
      hBaseline := app (baseline ++ `baseline_profile) (baseArgs.push hi) }

private def namedCost (e CB CD C : Expr) : Expr := e.replace fun e =>
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let a := e.getAppArgs
    if a[4]!.isApp && a[5]!.isApp && a[4]!.appFn! == CB && a[5]!.appFn! == CD &&
        a[4]!.appArg! == a[5]!.appArg! then some (mkApp C a[4]!.appArg!) else none
  else none

elab "publish_original_primary_raw_profile " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "actual primary raw profile: unknown mode"
  withData fun d => do
    let fixed := d.native[:44].toArray
    let CB := app (baseline ++ `Cbaseline) fixed
    let CD := app (raw ++ `Csource) d.fixed
    let hCB := app (baseline ++ `Cbaseline_nonneg) fixed
    let hCD := app (raw ++ `Csource_nonneg) d.fixed
    let C := app (root ++ `Craw) d.fixed
    if mode.getNat == 0 then
      let value ← termWith [(`CB,CB),(`CD,CD)] "(fun q : ℕ => CB q + CD q)"
      save `Craw d.fixed value (← inferType value) true
      return
    if mode.getNat == 1 then
      let value ← termWith [(`CB,CB),(`CD,CD),(`hCB,hCB),(`hCD,hCD)]
        "(fun q : ℕ => add_nonneg (hCB q) (hCD q))"
      let target := namedCost (← inferType value) CB CD C
      save `Craw_nonneg d.fixed value target
      return
    if mode.getNat == 2 then
      let value ← mkAppM ``HAdd.hAdd #[d.baseline,d.source]
      save `amplitude d.args value (← inferType value) true
      return
    let sourceZero := app (raw ++ `source_profile) (d.profileArgs.push (mkNatLit 0))
    let btype ← inferType d.hBaseline
    unless btype.isAppOfArity ``And 2 && btype.getAppArgs[0]!.isAppOfArity ``ContDiffOn 11 do
      throwError "actual primary raw profile: original baseline conjunction changed"
    let chart := btype.getAppArgs[0]!.getAppArgs[10]!
    unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
      throwError "actual primary raw profile: original whole source chart changed"
    let hChart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs
    let n := app ``Nat.succ #[d.native[0]!]
    let ambient := app `JanetCartan.embeddingDimension #[n]
    let hInitial ← mkAppM ``le_trans
      #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,d.native[45]!]
    let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts
      #[hInitial,d.native[46]!]
    let hR := part facts 0
    let R := (← inferType hR).appArg!
    let hT := part facts 1
    let T := (← inferType hT).appArg!
    let hh := part facts 3
    let h := (← inferType hh).appArg!
    let hTzero ← termWith [(`hT,hT)] "(zero_le_one : (0 : ℝ) ≤ 1).trans hT"
    let sourceJets ← withLocalDeclD `q (mkConst ``Nat) fun q => do
      let profile := app (raw ++ `source_profile) (d.profileArgs.push q)
      let hd := Expr.proj ``And 0 profile
      let hj := Expr.proj ``And 1 (Expr.proj ``And 1 profile)
      let price ← forallBoundedTelescope (← inferType hj) (some 1) fun sets bound => do
        unless sets.size == 1 && bound.isAppOfArity ``LE.le 4 do
          throwError "actual primary raw profile: raw global cNorm bound changed"
        return bound.appArg!
      let refl ← termWith [(`D,d.source),(`X,chart)] "(Set.eqOn_refl D X)"
      let converted := app `JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles.physical_jets_of_native
        #[n,ambient,d.source,d.source,chart,hChart,refl,hd,q,price,hj]
      mkLambdaFVars #[q] (Expr.proj ``And 1 converted)
    let A := app (root ++ `amplitude) d.args
    let eq ← termWith [(`A,A),(`B,d.baseline),(`D,d.source),(`X,chart)]
      "(show ∀ x ∈ X, A x = B x + D x from fun _ _ => rfl)"
    let hGlobal := Expr.proj ``And 0 sourceZero
    let globalType ← inferType hGlobal
    unless globalType.isAppOfArity ``ContDiff 10 do
      throwError "actual primary raw profile: global source smoothness changed"
    let ga := globalType.getAppArgs
    let hd := mkAppN (mkConst ``ContDiff.contDiffOn globalType.getAppFn.constLevels!)
      (ga[:8].toArray ++ #[chart,ga[9]!,ga[8]!,hGlobal])
    let proof := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeProfiles.complete_true_R_profile
      #[n,ambient,chart,hChart,A,d.baseline,d.source,eq,Expr.proj ``And 0 d.hBaseline,hd,
        CB,CD,hCB,hCD,T,R,h,hTzero,part facts 2,hR,part facts 4,
        Expr.proj ``And 1 d.hBaseline,sourceJets]
    let target := namedCost (← inferType proof) CB CD C
    if mode.getNat == 3 then
      save `profile_statement d.profileArgs target (mkSort .zero) true
    else
      save `profile d.profileArgs proof (app (root ++ `profile_statement) d.profileArgs)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfilesTemplate
end
