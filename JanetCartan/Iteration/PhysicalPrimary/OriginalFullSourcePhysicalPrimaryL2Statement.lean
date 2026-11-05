module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
public import JanetCartan.Iteration.PhysicalPairs.Assembly
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public meta import Lean

/-!
# Exact proposition for the actual primary L² consequence

Take order zero of the same full-source primary, use the existing physical
Plancherel identity, and enlarge only its scalar power at R ≥ 1. The chosen
coefficient remains before history, target, smoothing and external amplitude.
This leaf checks only the exact proposition and ordinary scalar conversion;
the separate proof leaf applies it to the genuine actual norm producer.
Consumer: the exact `hPL2` input of
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`
(`main:eq:primary-fixed-scales`, `main:eq:final-Cr`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Application
open Pseudodifferential PhysicalCutoff
private theorem physical_L2_of_zero_profile {n N : ℕ}
    (P : 𝓢(Euclidean n, Euclidean N)) (C δ R : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (h : (eLpNorm (fun ξ ↦ euclideanSobolevWeight (0 : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify P) ξ) 2 volume).toReal ≤
      C * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ ((0 : ℝ) - 1)) :
    PhysicalBernstein.physicalL2Norm P ≤ C * δ * R ^ RevisedScales.displacementLoss n := by
  rw [PhysicalPairs.physicalWeightedNorm_zero_eq_L2] at h
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ RevisedScales.forcingExponent n := by
    unfold RevisedScales.forcingExponent
    positivity
  have hc : 0 ≤ carrierExponent := by norm_num [carrierExponent]
  have hs : 0 ≤ samplingSlack := by norm_num [samplingSlack]
  have hexp : RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 - carrierExponent ≤
      RevisedScales.displacementLoss n := by
    unfold RevisedScales.displacementLoss
    linarith
  have hpow : R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
      (R ^ carrierExponent) ^ ((0 : ℝ) - 1) ≤ R ^ RevisedScales.displacementLoss n := by
    rw [← Real.rpow_mul hR0.le, ← Real.rpow_add hR0]
    convert Real.rpow_le_rpow_of_exponent_le hR hexp using 1
    congr 1
    ring
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hδ))
private theorem physical_L2_of_nat_zero_profile {n N : ℕ}
    (P : 𝓢(Euclidean n, Euclidean N)) (C δ R : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hR : 1 ≤ R)
    (h : (eLpNorm (fun ξ ↦ euclideanSobolevWeight ((0 : ℕ) : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify P) ξ) 2 volume).toReal ≤
      C * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ (((0 : ℕ) : ℝ) - 1)) :
    PhysicalBernstein.physicalL2Norm P ≤ C * δ * R ^ RevisedScales.displacementLoss n := by
  apply physical_L2_of_zero_profile P C δ R hC hδ hR
  simpa only [Nat.cast_zero] using h
end JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Application
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Application
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
private def profiles := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | t => t
private def bodyAt (name : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true) |
    throwError "actual primary L2: unavailable checked producer {name}"
  return head (value.beta p)
private def exactType (value : Expr) : MetaM Expr := do
  let ci ← getConstInfo value.getAppFn.constName!
  let mut type := ci.type.instantiateLevelParams ci.levelParams value.getAppFn.constLevels!
  for argument in value.getAppArgs do
    let .forallE _ _ tail _ := head type | throwError "actual primary L2: changed native application spine"
    type := tail.instantiate1 argument
  return head type
private def save (mode : Nat) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let statement := root ++ `L2_profiles_statement
  let resultType := if mode == 0 then mkSort .zero else app statement p
  let resultValue := if mode == 0 then target else proof
  let type ← instantiateMVars (← mkForallFVars p resultType)
  let value ← instantiateMVars (← mkLambdaFVars p resultValue)
  let env ← getEnv
  for expr in #[type,value] do
    let missing := expr.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual primary L2: missing original producer {missing.toList}"
    if expr.hasFVar || expr.hasMVar || expr.hasLevelMVar || expr.hasLevelParam || expr.hasLooseBVars || expr.hasSorry then
      throwError "actual primary L2: unresolved actual field or history DATA"
  if mode == 1 && !value.getUsedConstants.contains (root ++ `physical_profiles) then
    throwError "actual primary L2: genuine actual physical norm producer missing"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := if mode == 0 then statement else root ++ `L2_profiles
  let out ← liftM IO.getStdout
  liftM <| out.putStrLn s!"checking actual full-source primary L2 mode{mode}/{p.size}"
  liftM <| out.flush
  if mode == 0 then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME actual full-source physical primary has physical L2 norm at the literal revised displacementLoss, with a coefficient chosen before history/target/smoothing/external amplitude. Derived only from its genuine physical_profiles at q=0 and existing physical Plancherel; no analytic success premise (main:eq:primary-fixed-scales; RevisedStage.increment_estimates_of_physicalSobolev_profiles.hPL2)."
  logInfo m!"checked actual full-source primary L2 mode{mode}/{p.size}: actual q=0, Plancherel, revised displacementLoss"

elab "publish_actual_full_source_primary_L2 " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual primary L2: unknown statement/proof mode"
  let ci ← getConstInfo (root ++ `physical_profiles)
  forallBoundedTelescope ci.type (some 34) fun early proposition => do
    unless proposition.isAppOfArity (root ++ `physical_profiles_statement) 34 do
      throwError "actual primary L2: named actual profile proposition changed"
    let existsType ← bodyAt (root ++ `physical_profiles_statement) proposition.getAppArgs
    unless early.size == 34 && existsType.isAppOfArity ``Exists 2 do
      throwError "actual primary L2: actual prehistory profile34 changed"
    let Ctype := existsType.getAppArgs[0]!
    let predicate := existsType.getAppArgs[1]!
    let .sort level ← whnf (← inferType Ctype) | throwError "actual primary L2: unknown coefficient universe"
    let producer := app (root ++ `physical_profiles) early
    let C := mkAppN (mkConst ``Classical.choose [level]) #[Ctype,predicate,producer]
    let spec := mkAppN (mkConst ``Classical.choose_spec [level]) #[Ctype,predicate,producer]
    let pair := head (predicate.beta #[C])
    unless pair.isAppOfArity ``And 2 do throwError "actual primary L2: original coefficient positivity lost"
    let zero := mkNatLit 0
    let C0 := mkApp C zero
    let hC0 := mkApp (.proj ``And 0 spec) zero
    forallBoundedTelescope pair.getAppArgs[1]! (some 22) fun tail allOrders => do
      unless tail.size == 22 do throwError "actual primary L2: original history/numeric/amplitude tail changed"
      let .forallE _ _ zeroBody _ := head allOrders | throwError "actual primary L2: all physical orders lost"
      let zeroGoal := head (zeroBody.instantiate1 zero)
      unless zeroGoal.isAppOfArity ``LE.le 4 do throwError "actual primary L2: q=0 norm bound changed"
      let expectedP := app (root ++ `field) ((early[:33].toArray ++ tail[:19].toArray) ++ #[early[33]!,tail[20]!])
      let some complexP := zeroGoal.getAppArgs[2]!.find? (·.isAppOfArity `JanetCartan.PhysicalCutoff.complexify 3) |
        throwError "actual primary L2: original real Schwartz field lost"
      let fieldArgs := complexP.getAppArgs
      unless fieldArgs[2]! == expectedP do throwError "actual primary L2: q=0 concerns a different field"
      let literal ← bodyAt (root ++ `field) expectedP.getAppArgs
      unless literal.isAppOfArity (profiles ++ `selectedSourcePrimary) 53 do
        throwError "actual primary L2: field is not the frozen source-primary53"
      let native := literal.getAppArgs[:50].toArray
      let rates := app `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.stage_rates native
      let ratesType ← exactType rates
      unless ratesType.isAppOfArity ``And 2 && ratesType.getAppArgs[0]!.isAppOfArity ``LE.le 4 do
        throwError "actual primary L2: original current threshold certificate changed"
      let R := ratesType.getAppArgs[0]!.getAppArgs[3]!
      let hS := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray
      let hInitial ← mkAppM ``le_trans #[hS,native[45]!]
      let facts := app `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[native[44]!,hInitial,native[46]!]
      let factsType ← exactType facts
      let one ← mkNumeral (mkConst ``Real) 1
      unless factsType.isAppOfArity ``And 2 && factsType.getAppArgs[0]!.isAppOfArity ``LE.le 4 &&
          factsType.getAppArgs[0]!.getAppArgs[3]! == R do
        throwError "actual primary L2: history scale is not the SAME original R"
      unless ← isDefEq factsType.getAppArgs[0]!.getAppArgs[2]! one do
        throwError "actual primary L2: history fact does not prove one-le-R"
      let hR := .proj ``And 0 facts
      let hzero := mkAppN (.proj ``And 1 spec) (tail.push zero)
      let proof := app ``physical_L2_of_nat_zero_profile
        #[fieldArgs[0]!,fieldArgs[1]!,expectedP,C0,tail[20]!,R,hC0,tail[21]!,hR,hzero]
      let target ← exactType proof
      let allProof ← mkLambdaFVars tail proof
      let allType ← mkForallFVars tail target
      let .forallE _ _ positiveBody _ := head pair.getAppArgs[0]! |
        throwError "actual primary L2: coefficient positivity is not all-order"
      let positive := head (positiveBody.instantiate1 zero)
      let total := mkApp2 (mkConst ``And) positive allType
      let pairProof := mkAppN (mkConst ``And.intro) #[positive,allType,hC0,allProof]
      let real := mkConst ``Real
      let predicate ← withLocalDeclD `C real fun c => do
        mkLambdaFVars #[c] (total.replace fun e => if e == C0 then some c else none)
      let target := mkApp2 (mkConst ``Exists [.one]) real predicate
      let proof := mkAppN (mkConst ``Exists.intro [.one]) #[real,predicate,C0,pairProof]
      save mode.getNat early proof target
end JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Application
end

publish_actual_full_source_primary_L2 0
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.L2_profiles_statement
