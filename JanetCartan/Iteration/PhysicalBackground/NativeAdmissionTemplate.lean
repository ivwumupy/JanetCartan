module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Original-data closure of the same-density finite-low admission

Consumer: the native positive inverse/initial scalar and local primary waves.
Only the numerical original source interval and admissible history remain
inputs. The raw threshold is not assumed: its two halves are proved by the
same-history native comparison and the same-PhysicalSeed source construction.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeAdmissionTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

def targetNS := `JanetCartan.PhysicalBackground.NativeAdmission

def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq target actual do throwError "native admission: changed target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native admission: open or future-history dependence in {name}: valueFVar={value.hasFVar}, typeFVar={type.hasFVar}, valueMVar={value.hasMVar}, typeMVar={type.hasMVar}, valueLevel={value.hasLevelMVar}, typeLevel={type.hasLevelMVar}, valueSorry={value.hasSorry}, typeSorry={type.hasSorry}; {value}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

def component (proof : Expr) (i : Nat) : Expr :=
  .proj ``And 0 (Nat.repeat (fun p => Expr.proj ``And 1 p) i proof)

def rawSmallCode : String :=
  "by\n" ++
  "  let X := JanetCartan.CarrierSobolev.augmentedInputSobolevScale n Rows\n" ++
  "  let grade := kappa + (3 + (n - 1)) + 2\n" ++
  "  have hc : currentRaw ∈ X.level grade := currentMember grade\n" ++
  "  have hs : seedRaw ∈ X.level grade := (seedEstimate grade).1\n" ++
  "  have hd : currentRaw - seedRaw ∈ X.level grade := (X.level grade).sub_mem hc hs\n" ++
  "  have hadd := JanetCartan.ResponseTransfer.gradeNorm_add_le X hd hs\n" ++
  "  rw [sub_add_cancel] at hadd\n" ++
  "  have hCurrent : X.gradeNorm grade (currentRaw - seedRaw) ≤ delta / 2 := currentHalf\n" ++
  "  have hSeed : X.gradeNorm grade seedRaw ≤ delta / 2 := seedHalf\n" ++
  "  change X.gradeNorm grade currentRaw ≤ delta\n" ++
  "  linarith only [hadd, hCurrent, hSeed]"

elab "realize_native_current_density_admission" : command => liftTermElabM do
  let nativeNS := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let densityNS := `JanetCartan.PhysicalBackground.NativeDensity
  let sourceNS := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let budgetNS := `JanetCartan.PhysicalBackground.NativeRawSeedBudget
  let info ← getConstInfo (nativeNS ++ `rawCurrent)
  forallBoundedTelescope info.type (some 31) fun params _ => do
    unless params.size == 31 do throwError "native admission: expected exact native original31"
    let fixed := params[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[fixed[0]!, fixed[1]!, fixed[20]!]
    let selected := fixed.set! 20 capped
    let source (name : Name) := mkAppN (mkConst (sourceNS ++ name)) selected
    let order ← termWith [(`n, fixed[0]!)] "(2 * (n + 1) + 14 : ℕ)"
    let order ← store `admissionOrder fixed order true
    let h15 ← termWith [(`n, fixed[0]!), (`order, order)] "show 15 ≤ order from Nat.le_trans (Nat.le_succ 15) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.succ_le_succ (Nat.zero_le n))) 14)"
    discard <| store `admissionOrder_ge_fifteen fixed h15
    let δ ← store `threshold fixed
      (mkAppN (mkConst (densityNS ++ `threshold)) (fixed ++ #[order])) true
    let hδ ← store `threshold_pos fixed
      (mkAppN (mkConst (densityNS ++ `threshold_pos)) (fixed ++ #[order]))
    let budgetArgs := fixed ++ #[order, δ, hδ]
    let cap ← store `sourceCap fixed (mkAppN (mkConst (budgetNS ++ `halfCap)) budgetArgs) true
    discard <| store `sourceCap_pos fixed (mkAppN (mkConst (budgetNS ++ `halfCap_pos)) budgetArgs)
    discard <| store `sourceCap_le_current_inverse fixed
      (mkAppN (mkConst (budgetNS ++ `halfCap_le_current_inverse)) budgetArgs)
    discard <| store `sourceCap_le_strong fixed
      (mkAppN (mkConst (budgetNS ++ `halfCap_le_source)) budgetArgs)
    let inverseInterval ← termWith [(`sigma, params[21]!),
      (`inverseCap, mkAppN (mkConst (budgetNS ++ `currentInverseCap)) fixed)]
      "sigma ∈ Set.Ioc (0 : ℝ) inverseCap"
    unless ← isDefEq (← inferType params[22]!) inverseInterval do
      throwError "native admission: slot22 is not the retained current-normal-inverse cap"
    let chosen := #[source `χ, source `χ_smooth, source `χ_compact,
      mkAppN (mkConst `JanetCartan.PhysicalBackground.OriginalOuterCutoff.support_original) selected,
      source `X0, source `X0_smooth]
    for (name, value) in #[(`χ, chosen[0]!), (`X0, chosen[4]!)] do
      discard <| store name fixed value true
    let rawAtOrder := mkAppN (mkConst (nativeNS ++ `rawCurrent)) (params ++ chosen ++ #[order])
    forallBoundedTelescope (← inferType rawAtOrder) (some 1) fun reserve _ => do
      unless reserve.size == 1 do throwError "native admission: the original numerical reserve changed"
      let prehistory := params ++ chosen ++ #[order] ++ reserve ++ #[δ, hδ]
      unless prehistory.size == 41 do throwError "native admission: native original41 specialization failed"
      let shallow := params ++ reserve
      discard <| store `S shallow (mkAppN (mkConst (nativeNS ++ `S)) prehistory) true
      discard <| store `hS shallow (mkAppN (mkConst (nativeNS ++ `hS)) prehistory)
      let scaleType ← termWith [(`sigma, params[21]!), (`cap, cap)] "sigma ∈ Set.Ioc (0 : ℝ) cap"
      withLocalDeclD `hσbackground scaleType fun hσbackground => do
        let seeded := fixed ++ #[params[21]!, params[23]!] ++ chosen
        let seedRaw := mkAppN (mkConst (nativeNS ++ `rawSeed)) seeded
        let seedEstimate := mkAppN (mkConst (nativeNS ++ `rawSeed_preScale_estimate)) seeded
        let seedHalf := mkAppN (mkConst (budgetNS ++ `half_native))
          (budgetArgs ++ #[params[21]!, hσbackground, params[23]!])
        let rawAt := mkAppN (mkConst (nativeNS ++ `rawCurrent)) prehistory
        forallTelescope (← inferType rawAt) fun history _ => do
          unless history.size == 6 do throwError "native admission: native R0/history6 changed"
          let full := prehistory ++ history
          let inputs := shallow ++ #[hσbackground] ++ history
          let native (name : Name) := mkAppN (mkConst (nativeNS ++ name)) full
          let density (name : Name) := mkAppN (mkConst (densityNS ++ name)) full
          let raw ← store `raw inputs (native `rawCurrent) true
          let datum ← store `measuredSource inputs (native `measuredDatum) true
          let v ← store `v inputs (density `v) true
          discard <| store `current inputs (native `current) true
          discard <| store `physicalMean inputs (density `physicalMean) true
          let vType ← whnf (← inferType v)
          let .forallE _ index _ _ := vType |
            throwError "native admission: current density lost its original carrier index"
          let admission := density `admission_from_raw_small
          let .forallE _ smallType _ _ ← whnf (← inferType admission) |
            throwError "native admission: actual same-density threshold premise missing"
          let small ← termWith [(`n, fixed[0]!), (`Rows, index), (`kappa, order), (`delta, δ),
            (`currentRaw, raw), (`seedRaw, seedRaw), (`currentMember, native `rawCurrent_mem),
            (`seedEstimate, seedEstimate), (`currentHalf, native `raw_half), (`seedHalf, seedHalf)]
            rawSmallCode (some smallType)
          let small ← store `raw_small inputs small
          let admitted := mkApp admission small
          let replace (type : Expr) := type.replace fun e =>
            if e == density `v then some v else if e == native `rawCurrent then some raw
            else if e == native `measuredDatum then some datum else none
          let admitted ← store `admitted inputs admitted false (some (replace (← inferType admitted)))
          for (name, i) in #[(`smooth, 0), (`ae, 1), (`range, 2), (`labels_smooth, 3),
              (`labels_low, 4), (`global_estimate, 5), (`label_estimate, 6)] do
            discard <| store name inputs (component admitted i)
          let labelSmooth := component admitted 3
          let low := component admitted 4
          let C15 ← termWith [(`order15, h15), (`low, low)]
            "fun i ↦ (JanetCartan.cNorm_mono_order order15).trans (low i)"
          discard <| store `labels_C15 inputs C15
          let labels ← withLocalDeclD `i index fun i => do
            let value ← mkAppM `JanetCartan.PositiveBackground.densityOnInitialLabels #[mkApp v i]
            mkLambdaFVars #[i] value
          let labels ← store `labels inputs labels true
          let labelsRange ← termWith [(`labels, labels), (`range, component admitted 2)]
            "show ∀ i q, 1 + labels i q ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) from fun i q ↦ range i _"
          let labelsRange ← store `labels_range inputs labelsRange
          let initial := Nat.repeat (fun p => Expr.proj ``And 1 p) 7 admitted
          let initial := mkAppN initial #[params[21]!, ← mkAppM ``And.left #[params[23]!]]
          discard <| store `initial_smooth inputs (.proj ``And 0 initial)
          discard <| store `initial_pos inputs (.proj ``And 0 (.proj ``And 1 initial))
          discard <| store `initial_sq inputs (.proj ``And 1 (.proj ``And 1 initial))
          -- Apply the original universal positive branch to THESE labels and
          -- proofs. Its operator remains existential, for the same inverse
          -- consumer to select; no independent operator is selected here.
          let mut positive := mkApp (native `all_densities) labels
          for code in #[
              "by intro i; exact (labelSmooth i).contDiffOn",
              "by intro i q _; have h := labelRange i q; linarith [h.1]",
              "by intro i q _; exact labelRange i q",
              "by intro i; exact canonicalLow i"] do
            let .forallE _ domain _ _ ← whnf (← inferType positive) |
              throwError "native admission: native positive density class changed"
            let proof ← termWith [(`labelSmooth, labelSmooth), (`labelRange, labelsRange), (`canonicalLow, low)]
              code (some domain)
            positive := mkApp positive proof
          discard <| store `positive_inverse_exists inputs positive
          logInfo "actual SAME NativeDensity.v admitted from proved current/reference halves; protected chi, fresh X0, labels C15 and universal positive inverse packet; no raw-smallness premise"

end JanetCartan.PhysicalBackground.NativeAdmissionTemplate
end
