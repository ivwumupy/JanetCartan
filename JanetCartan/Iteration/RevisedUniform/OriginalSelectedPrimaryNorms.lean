module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# The same actual primary's early coefficient in the revised step

Choose the already proved physical norm coefficient BEFORE every history,
target, smoothing order and external amplitude. Retain its exact primary
profile for hPSob, and weaken only the scalar R-power for hHigh of
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`. The Schwartz
field is literally OriginalFullSourcePhysicalPrimary.field54 on the one
complete-forcing sample. No primary strain estimate is asserted here
(`main:eq:primary-fixed-scales`, `main:eq:joint-physical-profile`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.RevisedUniform.OriginalSelectedPrimaryNormsTemplate
open Pseudodifferential PhysicalCutoff
private theorem revised_primary_profile {n N : ℕ} (q : ℕ)
    (P : 𝓢(Euclidean n, Euclidean N)) {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (h : (eLpNorm (fun ξ ↦ euclideanSobolevWeight (q : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify P) ξ) 2 volume).toReal ≤
      C * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ ((q : ℝ) - 1)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight (q : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify P) ξ) 2 volume).toReal ≤
      C * δ * R ^ RevisedScales.displacementLoss n * (R ^ carrierExponent) ^ (q : ℝ) := by
  have hA : 0 ≤ RevisedScales.forcingExponent n := by
    unfold RevisedScales.forcingExponent
    positivity
  have hcarrier : 0 ≤ carrierExponent := by norm_num [carrierExponent]
  have hslack : 0 ≤ samplingSlack := by norm_num [samplingSlack]
  have hpower : RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 ≤
      RevisedScales.displacementLoss n := by
    unfold RevisedScales.displacementLoss
    linarith
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hCarrierScale : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR hcarrier
  have hlarge := Real.rpow_le_rpow_of_exponent_le hR hpower
  have horder := Real.rpow_le_rpow_of_exponent_le hCarrierScale (by linarith : (q : ℝ) - 1 ≤ (q : ℝ))
  exact h.trans (by gcongr)
end JanetCartan.RevisedUniform.OriginalSelectedPrimaryNormsTemplate
end
public meta section
namespace JanetCartan.RevisedUniform.OriginalSelectedPrimaryNormsTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms
private def source := `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | t => t
private def bodyAt (name : Name) (p : Array Expr) : MetaM Expr := do
  let ci ← getConstInfo name
  let some value := ci.value? (allowOpaque := true) | throwError "actual primary norm packing: unavailable body {name}"
  return head ((value.instantiateLevelParams ci.levelParams []).beta p)
private def exactType (value : Expr) : MetaM Expr := do
  let ci ← getConstInfo value.getAppFn.constName!
  let mut type := ci.type.instantiateLevelParams ci.levelParams value.getAppFn.constLevels!
  for argument in value.getAppArgs do
    let .forallE _ _ tail _ := head type | throwError "actual primary norm packing: changed producer spine"
    type := tail.instantiate1 argument
  return head type
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual primary norm packing: later or unresolved input in {key}"
  unless value.getUsedConstants.contains (source ++ `physical_profiles) do
    throwError "actual primary norm packing: genuine physical norm producer not consumed"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Checking actual selected primary norm {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "One actual full-source primary coefficient selected before history/target/smoothing/amplitude, applied to the unchanged field54 with exact physical 2pi norm. The high-profile variant weakens only scalar powers at the proved original R>=1. No source/profile/strain success premise (main:eq:primary-fixed-scales; main:eq:joint-physical-profile)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary norm packing: nonstandard axioms {ax}"
  logInfo m!"PASS actual selected primary norm {key}/{p.size}: {ax}"
elab "pack_actual_selected_primary_norm " mode:num : command => liftTermElabM do
  unless mode.getNat < 4 do throwError "actual primary norm packing: unknown mode"
  forallBoundedTelescope (← getConstInfo (source ++ `physical_profiles)).type (some 34) fun early proposition => do
    unless proposition.isAppOfArity (source ++ `physical_profiles_statement) 34 do
      throwError "actual primary norm packing: original statement34 changed"
    let existsType ← bodyAt (source ++ `physical_profiles_statement) proposition.getAppArgs
    unless early.size == 34 && existsType.isAppOfArity ``Exists 2 do
      throwError "actual primary norm packing: prehistory existential changed"
    let Ctype := existsType.getAppArgs[0]!
    let predicate := existsType.getAppArgs[1]!
    let .sort level ← whnf (← inferType Ctype) | throwError "actual primary norm packing: coefficient universe"
    let producer := app (source ++ `physical_profiles) early
    let C := mkAppN (mkConst ``Classical.choose [level]) #[Ctype,predicate,producer]
    let spec := mkAppN (mkConst ``Classical.choose_spec [level]) #[Ctype,predicate,producer]
    let pair := head (predicate.beta #[C])
    unless pair.isAppOfArity ``And 2 do throwError "actual primary norm packing: positivity missing"
    let named := app (root ++ `CP) early
    let rename (t : Expr) := t.replace fun e => if e == C then some named else none
    if mode.getNat == 0 then
      save `CP early C Ctype true
    else if mode.getNat == 1 then
      save `CP_nonneg early (.proj ``And 0 spec) (rename pair.getAppArgs[0]!)
    else if mode.getNat == 2 then
      save `physical_profile early (.proj ``And 1 spec) (rename pair.getAppArgs[1]!)
    else
      forallBoundedTelescope pair.getAppArgs[1]! (some 23) fun tail target => do
        unless tail.size == 23 && target.isAppOfArity ``LE.le 4 do
          throwError "actual primary norm packing: original data/amplitude/order tail changed"
        let q := tail[22]!
        let P := app (source ++ `field) ((early[:33].toArray ++ tail[:19].toArray) ++ #[early[33]!,tail[20]!])
        let some complexP := target.getAppArgs[2]!.find? (·.isAppOfArity `JanetCartan.PhysicalCutoff.complexify 3) |
          throwError "actual primary norm packing: original Schwartz field missing"
        let fieldArgs := complexP.getAppArgs
        unless fieldArgs[2]! == P do throwError "actual primary norm packing: different primary field"
        let literal ← bodyAt (source ++ `field) P.getAppArgs
        unless literal.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary 53 do
          throwError "actual primary norm packing: not the original source primary53"
        let native := literal.getAppArgs[:50].toArray
        let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
        let hInitial ← mkAppM ``le_trans
          #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray,native[45]!]
        let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
        let factsType := head (← inferType facts)
        let requiredScale ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 1,R]
        unless factsType.isAppOfArity ``And 2 && (← isDefEq factsType.getAppArgs[0]! requiredScale) do
          throwError "actual primary norm packing: not exactly 1≤the SAME historyScale R"
        let hR := .proj ``And 0 facts
        let hC := mkApp (.proj ``And 0 spec) q
        let raw := mkAppN (.proj ``And 1 spec) tail
        let proof := app ``revised_primary_profile
          #[fieldArgs[0]!,fieldArgs[1]!,q,P,mkApp named q,tail[20]!,R,hC,tail[21]!,hR,raw]
        save `high_profile early (← mkLambdaFVars tail proof) (← mkForallFVars tail (← exactType proof))
pack_actual_selected_primary_norm 0
pack_actual_selected_primary_norm 1
pack_actual_selected_primary_norm 2
pack_actual_selected_primary_norm 3
end JanetCartan.RevisedUniform.OriginalSelectedPrimaryNormsTemplate
end
#print axioms JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms.CP
#print axioms JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms.CP_nonneg
#print axioms JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms.physical_profile
#print axioms JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms.high_profile
