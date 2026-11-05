module

public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication

/-!
# The retained before-history physical envelope costs

Publish the unchanged original static45 costs and their proved nonnegativity
once, separately from spatial and displacement consequences. The three raw
costs and their positivity are read from the same frozen97 native budget;
source size enters the displacement cost exactly once. Every profile precedes
R and physical history, on the original row and original retained parent
(`app:ch_response:eq:current-atomic-amplitudes`, `main:eq:primary-fixed-scales`).

The Application leaf consumes these exact declarations without replaying or
reselecting any budget. No analytic success premise or resource override is
introduced.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeBudgetTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeTemplate
open JanetCartan.PhysicalMean.OriginalParentCorrectedProfilesTemplate
open JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
open JanetCartan.PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def physical := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def tail (e : Expr) (k : Nat) := Nat.repeat (fun v => Expr.proj ``And 1 v) k e
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (tail e k)
private def exactType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "actual corrected application: declaration arity changed"
    type := rest.instantiate1 arg
  return type

private def applyThrough (name last : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut value := mkConst name
  while let .forallE key _ rest _ := type.consumeMData do
    let some (_,arg) := known.find? (·.1 == key) |
      throwError "actual corrected application: missing exact {name}.{key}"
    value := mkApp value arg
    if key == last then return value
    type := rest
  throwError "actual corrected application: missing last argument {last}"
private def emit (key : Name) (xs : Array Expr) (v : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual envelope application: checking {key}"
  -- Do not eagerly infer the enormous native term when its exact type is known.
  -- The kernel still checks the declaration against that explicit type below.
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  let resultType ← match target with
    | some t => pure t
    | none => inferType v
  let type ← instantiateMVars (← mkForallFVars xs resultType)
  if type.hasFVar || type.hasMVar || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "actual corrected application: open or incomplete declaration {name}"
  if data then
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  let out := mkAppN (mkConst name) xs
  addDocStringCore (ns ++ key)
    "Actual same-native-scalar corrected parent response jet, with original uncut response and no new field or cutoff (main:eq:primary-fixed-scales)."
  logInfo m!"actual original corrected envelope application: checked {key} / {xs.size}"
  return out

private def retainedBudgetProof (xs : Array Expr) (mode : Nat) : MetaM (Expr × Expr) := do
  let info ← getConstInfo `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native.A_nonneg
  let some value := info.value? (allowOpaque := true) |
    throwError "actual corrected application: frozen budget nonnegativity proof is unavailable"
  let proof := (value.beta xs).headBeta
  unless proof.isAppOfArity `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.correctedCost_nonneg 12 do
    throwError "actual corrected application: frozen budget nonnegativity spine changed"
  let args := proof.getAppArgs
  let applied := mkAppN proof.getAppFn args[:7+mode].toArray
  let .forallE _ target _ _ := (← exactType applied).consumeMData |
    throwError "actual corrected application: frozen budget proof domain changed"
  return (args[7+mode]!,target)

private def withStaticCosts (go : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native.A
  let some body := info.value? (allowOpaque := true) |
    throwError "actual corrected application: frozen native45 cost is unavailable"
  bindNative 45 info.type #[] fun xs => do
    let cost := (body.beta xs).headBeta
    unless cost.isAppOfArity `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.correctedCost 7 do
      throwError "actual corrected application: frozen corrected cost spine changed"
    go xs cost.getAppArgs
where
  bindNative : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,xs,next => next xs
    | remaining+1,type,xs,next => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual corrected application: native45 ended at {xs.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        bindNative remaining (body.instantiate1 x) (xs.push x) next

elab "publish_native_corrected_static_budget " mode:num : command => liftTermElabM do
  withStaticCosts fun xs costs => do
    let keys : Array (Name × Name × Nat) :=
      #[(`Pξ,`Pξ_nonneg,2),(`Clead,`Clead_nonneg,3),(`Ccorr,`Ccorr_nonneg,4)]
    unless mode.getNat < keys.size do throwError "actual corrected application: unknown static cost"
    let (key,nonnegKey,position) := keys[mode.getNat]!
    let cost := costs[position]!
    let target ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    let named ← emit key xs cost true (some target)
    liftM <| IO.eprintln "actual static budget: reading frozen nonnegativity"
    let (h,originalType) ← retainedBudgetProof xs mode.getNat
    let hType := originalType.replace fun e => if e == cost then some named else none
    unless (hType.find? (· == named)).isSome do
      throwError "actual corrected application: static nonnegative cost alias changed"
    discard <| emit nonnegKey xs h false (some hType)

elab "publish_native_corrected_static_combined_cost " mode:num : command => liftTermElabM do
  withPublishedNativeStage fun g => do
    let p := g.params44.push g.data.i
    let target ← mkArrow (mkConst ``Nat) (mkConst ``Real)
    if mode.getNat == 0 then
      let A := app (ns ++ `Clead) p
      let B := app (ns ++ `Ccorr) p
      let D := app (physical ++ `Cdisp) g.physical44
      let hD := app (physical ++ `Cdisp_nonneg) g.physical44
      let σ := g.data.native33[21]!
      let hσ ← mkAppM `le_of_lt #[Expr.proj ``And 0 g.data.native33[23]!]
      let literal := app (ns ++ `correctedDisplacementCost) #[A,B,D,σ]
      let cost ← emit `Adisp p literal true (some target)
      let proof := app (ns ++ `correctedDisplacementCost_nonneg)
        #[A,B,D,σ,app (ns ++ `Clead_nonneg) p,app (ns ++ `Ccorr_nonneg) p,hD,hσ]
      let proofType := (← exactType proof).replace fun e => if e == literal then some cost else none
      discard <| emit `Adisp_nonneg p proof false (some proofType)
    else if mode.getNat == 1 then
      let sharp := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
      let one ← mkNumeral (mkConst ``Real) 1
      let hOne ← termWith [] "(show (0 : ℝ) ≤ 1 from zero_le_one)"
      let cf := app (sharp ++ `Cfrequency) g.data.sampler22
      let hcf ← mkAppM `le_trans #[hOne,app (sharp ++ `Cfrequency_ge_one) g.data.sampler22]
      let A := app (ns ++ `Adisp) p
      let P := app (ns ++ `Pξ) p
      let literal := app (sharp ++ `sharpJetCost) #[one,cf,A,P]
      let cost ← emit `Cphysical p literal true (some target)
      let proof := app (sharp ++ `sharpJetCost_nonneg)
        #[one,cf,hOne,hcf,A,P,app (ns ++ `Adisp_nonneg) p,app (ns ++ `Pξ_nonneg) p]
      let proofType := (← exactType proof).replace fun e => if e == literal then some cost else none
      discard <| emit `Cphysical_nonneg p proof false (some proofType)
    else throwError "actual corrected application: unknown combined cost"

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelopeBudgetTemplate
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_native_corrected_static_budget 0
publish_native_corrected_static_budget 1
publish_native_corrected_static_budget 2
publish_native_corrected_static_combined_cost 0
publish_native_corrected_static_combined_cost 1

end
