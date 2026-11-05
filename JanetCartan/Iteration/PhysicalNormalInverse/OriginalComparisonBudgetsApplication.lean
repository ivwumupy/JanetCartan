module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfiles
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalWorkingProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicHighPass
public meta import Lean

/-!
# Before-history comparison constants on the actual original sampler

Apply the ONE retained Comparison continuation to the actual original common
measurement and retained five-field budget, the literal large cutoff, original
variable-radius sampling weight, detector and high-pass. The response budget
and common quadrature kernel are fixed before every history. The actual high
initial profile and uncut full-response inputs still belong to the current
continuation: this static cache does not assert the finite corrected-normal
estimate (`app:ch_waves:eq:colored-normal-comparison`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

private theorem support_image_of_tsupport {E F : Type*} [TopologicalSpace E]
    {κ : E → ℝ} {g : E → F} {S : Set F} (h : g '' tsupport κ ⊆ S) :
    g '' Function.support κ ⊆ S :=
  (image_mono (subset_tsupport κ)).trans h

private theorem source_support_min {E : Type*} [TopologicalSpace E] {n : ℕ}
    {κ : E → ℝ} {g : E → Euclidean n} {s₁ s₂ : ℝ}
    (h : g '' tsupport κ ⊆ closedBall 0 (min s₁ s₂ / 4)) :
    g '' Function.support κ ⊆ closedBall 0 (s₂ / 4) :=
  (support_image_of_tsupport h).trans
    (closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)))

private theorem mem_closedBall_min {E : Type*} [PseudoMetricSpace E]
    {x c : E} {a b : ℝ} (h : x ∈ closedBall c (min a b)) :
    x ∈ closedBall c b := closedBall_subset_closedBall (min_le_right _ _) h

private theorem mem_closedBall_min_half {E : Type*} [PseudoMetricSpace E]
    {x c : E} {a b : ℝ} (h : x ∈ closedBall c (min a b / 2)) :
    x ∈ closedBall c (b / 2) :=
  closedBall_subset_closedBall
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h

private theorem quarter_positive : (0 : ℝ) < 1 / 4 := by norm_num

private theorem coefficient_ball_subset (n : ℕ) {b R : ℝ} (h : b < R) :
    closedBall (0 : Euclidean n) b ⊆ ball 0 R := closedBall_subset_ball h

private theorem working_geometry {n : ℕ}
    (center : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {r : ℝ} (hr : 0 < r) :
    IsCompact (closedBall center r) ∧ IsOpen (ball center (2 * r)) ∧
      closedBall center r ⊆ ball center (2 * r) :=
  ⟨isCompact_closedBall _ _, isOpen_ball, closedBall_subset_ball (by linarith)⟩

private theorem original_high_zero (n : ℕ) :
    ∀ η : Euclidean (n - 1), ‖η‖ ≤ 1 → ContinuumRow.FixedCutoffs.highFrequency ‖η‖ = 0 :=
  fun _ h ↦ ContinuumRow.FixedCutoffs.highFrequency_zero h

private theorem original_high_one (n : ℕ) :
    ∀ η : Euclidean (n - 1), 2 ≤ ‖η‖ → ContinuumRow.FixedCutoffs.highFrequency ‖η‖ = 1 :=
  fun _ h ↦ ContinuumRow.FixedCutoffs.highFrequency_one h

end JanetCartan.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
end

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalNormalInverse.OriginalComparison
private def currentNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
private def choicesNS := `JanetCartan.PhysicalSampling.OriginalChoices
private def weightsNS := `JanetCartan.PhysicalSampling.OriginalWeights
private def profilesNS := `JanetCartan.PhysicalNormalInverse.OriginalRetained
private def measurementNS := `JanetCartan.PhysicalNormalInverse.OriginalMeasurement

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  if (← whnf (← inferType proof)).isAppOfArity ``And 2 then
    mkAppM ``And.left #[proof]
  else pure proof

private def conjunction (proofs : Array Expr) : MetaM Expr := do
  let mut result := proofs.back!
  for i in (List.range (proofs.size - 1)).reverse do
    result ← mkAppM ``And.intro #[proofs[i]!, result]
  return result

private def traceStage (message : String) : MetaM Unit := logInfo message

private def store (short : Name) (params : Array Expr) (value : Expr)
    (data := false) (target : Option Expr := none) : MetaM Expr := do
  let resultType := target.getD (← inferType value)
  unless ← withTransparency .default <| isDefEq resultType (← inferType value) do
    throwError "original comparison budget: target mismatch {short}"
  let type ← instantiateMVars (← mkForallFVars params resultType)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasSorry ||
      type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasSorry then
    throwError "original comparison budget: incomplete declaration {short}"
  let name := root ++ short
  traceStage s!"original comparison: kernel check {short}"
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  return mkAppN (mkConst name) params

private def applyInputs (fn : Expr) (args : Array Expr) : MetaM Expr := do
  traceStage s!"original comparison: apply {args.size} exact retained inputs"
  let result := mkAppN fn args
  discard <| inferType result
  return result

private def nonnegative (positive : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType positive) (some 1) fun orders _ => do
    mkLambdaFVars orders (← mkAppM `le_of_lt #[mkApp positive orders[0]!])

/-- Apply all fixed geometry, actual budgets and original mask inputs before
choosing Ccompare. The remaining response budget is explicit until task13's
actual full-response producer is joined; no finite comparison is assumed. -/
private def cacheActualComparison : MetaM Unit := withTransparency .reducible do
  traceStage "original comparison: begin exact actual factory command"
  withLocalDeclD `m (mkConst ``Nat) fun m => do
    let samplingInfo ← getConstInfo `JanetCartan.PhysicalSampling.samplingCappedExtra
    let samplingTail := samplingInfo.type.bindingBody!.instantiate1 m
    let n := samplingTail.bindingDomain!.appArg!
    let current := mkApp (mkConst (currentNS ++ `current)) n
    forallBoundedTelescope (← inferType current) (some 20) fun base _ => do
      withLocalDeclD `pOrder (mkConst ``Nat) fun pOrder => do
        let hn := base[0]!
        let weightsArgs := #[m, hn, pOrder] ++ base[1:20].toArray
        let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
          #[m, hn, pOrder, base[19]!]
        let raw := (#[n] ++ base).set! 20 merged
        let native := mkAppN (mkConst (currentNS ++ `current)) raw
        forallBoundedTelescope (← inferType native) (some 10) fun fixedTail _ => do
          let fixed := raw ++ fixedTail
          let profileStart := mkAppN (mkConst (profilesNS ++ `Budgets.Mgeom)) fixed
          let profileStartType ← whnf (← inferType profileStart)
          let indexType := profileStartType.bindingDomain!
          withLocalDeclD `i indexType fun i => do
            let profileBase := fixed.push i
            let profilePrefix := mkAppN (mkConst (profilesNS ++ `Budgets.Mgeom)) profileBase
            forallBoundedTelescope (← inferType profilePrefix) (some 2) fun initialBudget _ => do
              unless fixed.size == 31 && initialBudget.size == 2 do
                throwError "original comparison: expected native31 and positive-initial budget pair"
              let profiles := profileBase ++ initialBudget
              traceStage "original comparison: native31 and SAME before-history five-field tuple prepared"
              let params := weightsArgs ++ fixedTail ++ #[i] ++ initialBudget
              let profile (name : Name) := mkAppN (mkConst (profilesNS ++ `Budgets ++ name)) profiles
              let measured (name : Name) := mkAppN (mkConst (measurementNS ++ name)) fixed
              let profileS := mkAppN (mkConst (profilesNS ++ `S)) profiles
              let measureS := measured `S
              discard <| store `S params (← mkAppM ``Max.max #[measureS, profileS]) true
              let hMeasured ← store `S_measurement params (← mkAppM `le_max_left #[measureS, profileS])
              let hProfiles ← store `S_profiles params (← mkAppM `le_max_right #[measureS, profileS])
              discard <| store `S_native params (← mkAppM `le_trans
                #[mkAppN (mkConst (profilesNS ++ `S_native)) profiles, hProfiles])
              discard <| store `hS params (← mkAppM `le_trans #[measured `hS, hMeasured])
              let selectedArgs := raw.set! 20
                (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n, hn, merged])
              let selected (name : Name) := mkAppN (mkConst (selectedNS ++ name)) selectedArgs
              let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
              let l ← mkAppM ``Sigma.snd #[i]
              let cell := mkAppN (selected `cell) #[q, l]
              let hroot := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.root_mem)
                (weightsArgs ++ #[q, l])
              let geometry := #[m, pOrder, hn, q, l, cell, hroot]
              let choice (part name : Name) := mkAppN (mkConst (choicesNS ++ part ++ name)) geometry
              let weight (name : Name) := mkAppN (mkConst (weightsNS ++ name)) weightsArgs
              let admission (name : Name) := mkAppN
                (mkConst (`JanetCartan.PhysicalSampling.OriginalAdmission ++ name)) (weightsArgs.push i)
              let factory := choice `Comparison `continuation
              let ftype ← whnf (← inferType factory)
              let KFtype := ftype.bindingDomain!
              let zero ← mkAppOptM ``OfNat.ofNat #[some KFtype.appArg!, some (mkNatLit 0), none]
              let b := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b) #[n, hn]
              let KF ← mkAppM `Metric.closedBall #[zero, b]
              let hKF ← mkAppM `ProperSpace.isCompact_closedBall #[zero, b]
              let hbR := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.b_lt_R) #[n, hn]
              let hKFU ← mkAppM ``coefficient_ball_subset #[n, hbR]
              let rootType ← inferType hroot
              let rootProduct ← Core.betaReduce rootType
              let some originalT := rootProduct.find? (fun e =>
                  e.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.εcarrier 4)
                | throwError "original comparison: missing actual selected original patch"
              let patch := originalT.getAppArgs[2]!
              let hball := mkAppN (mkConst `JanetCartan.PhysicalInitialization.original_frameBall_subset)
                #[n, hn, patch]
              traceStage "original comparison: SAME root, coefficient ball and original frame-ball inclusion prepared"
              let hQuarter := mkConst ``quarter_positive
              let quarter := (← inferType hQuarter).getAppArgs.back!
              let budgetInputs := #[KF, hKF, hKFU, hball, profile `Mgeom, quarter, profile `gnormal,
                hQuarter, profile `fact2, measured `Budgets.Cmeasure,
                ← nonnegative (measured `Budgets.positive), profile `Pξ, profile `Clead,
                profile `Ccorr, profile `Clead, profile `Ccorr]
              let factory ← applyInputs factory budgetInputs
              forallBoundedTelescope (← inferType factory) (some 1) fun response _ => do
                let factory ← applyInputs factory (response ++ #[
                  ← nonnegative (profile `fact3), ← nonnegative (profile `fact5),
                  ← nonnegative (profile `fact6), ← nonnegative (profile `fact5),
                  ← nonnegative (profile `fact6)])
                forallBoundedTelescope (← inferType factory) (some 1) fun responseSign _ => do
                  let factory := mkApp factory responseSign[0]!
                  let hSupport := choice `Cutoff `hκ_support
                  let K := (← inferType hSupport).getAppArgs.back!
                  let Kargs := K.getAppArgs
                  let center := Kargs[Kargs.size - 2]!
                  let radiusPair := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius)
                    #[n, hn, q, l, cell]
                  let hrho ← mkAppM ``Subtype.property #[radiusPair]
                  let hGeometry ← mkAppM ``working_geometry #[center, hrho]
                  let hK ← component hGeometry 0
                  let hΩ ← component hGeometry 1
                  let hKΩ ← component hGeometry 2
                  let Ω := (← inferType hΩ).getAppArgs.back!
                  let hη := mkApp (selected `hηb) i
                  let hr := mkApp (selected `hr') i
                  let detector ← mkAppM `JanetCartan.Sampling.originalConicDetector #[hη, hr]
                  let hDetector := mkAppN
                    (mkConst `JanetCartan.Sampling.originalConicDetector_contDiffAt) detector.getAppArgs
                  let hHom := mkAppN
                    (mkConst `JanetCartan.Sampling.originalConicDetector_homogeneous) detector.getAppArgs
                  let hHigh := mkApp (mkConst `JanetCartan.Sampling.contDiff_originalConicHighPass) n
                  let high := (← inferType hHigh).getAppArgs.back!
                  let cutoffInputs := #[K, Ω, hK, hΩ, hKΩ, choice `Cutoff `κ,
                    choice `Cutoff `hκ, choice `Cutoff `hκ_compact, hSupport,
                    ← mkAppM ``support_image_of_tsupport #[choice `Cutoff `hκ_radius],
                    ← mkAppM ``source_support_min #[choice `Cutoff `hκ_s],
                    detector, high, hDetector, hHom, hHigh,
                    mkApp (mkConst ``original_high_zero) n, mkApp (mkConst ``original_high_one) n]
                  let factory ← applyInputs factory cutoffInputs
                  let factory ← forallBoundedTelescope (← inferType factory) (some 2) fun radial _ => do
                    let proofs ← radial.mapM fun premise => do
                      let typ ← inferType premise
                      mkAppM `le_refl #[typ.getAppArgs.back!]
                    applyInputs factory proofs
                  let hPsiSupport := choice `Cutoff `hψ_support
                  let hPsiSupport ← forallBoundedTelescope (← inferType hPsiSupport) (some 3) fun inputs _ => do
                    let body := mkAppN hPsiSupport inputs
                    mkLambdaFVars inputs (← conjunction #[← component body 0, ← component body 1,
                      ← mkAppM ``mem_closedBall_min #[← component body 2],
                      ← mkAppM ``mem_closedBall_min_half #[← component body 3]])
                  let hCutoff := admission `cutoff_on_actual_selected_row
                  let weightPlateau ← component hCutoff 5
                  let weightPlateau ← forallBoundedTelescope (← inferType weightPlateau) (some 2) fun inputs _ => do
                    mkLambdaFVars inputs (← mkAppM ``And.left #[mkAppN weightPlateau inputs])
                  let one ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 1), none]
                  let factory ← applyInputs factory #[admission `comparison_detector_support,
                    choice `Cutoff `ψ, choice `Cutoff `Bψ, choice `Cutoff `hψ,
                    choice `Cutoff `hψ_bounds, hPsiSupport, mkApp (weight `φ) i,
                    weight `B, one, mkApp (weight `patchBounds) i, mkApp (weight `smooth) i, weightPlateau]
                  forallBoundedTelescope (← inferType factory) (some 9) fun quadrature _ => do
                    let actual ← applyInputs factory quadrature
                    let full := params ++ response ++ responseSign ++ quadrature
                    let initialized ← store `initialized full actual
                    let Ccompare ← store `Ccompare full (← mkAppM ``Classical.choose #[initialized]) true
                    let specType := (← whnf (← inferType initialized)).appArg!.beta #[Ccompare]
                    let spec ← store `spec full (← mkAppM ``Classical.choose_spec #[initialized]) false (some specType)
                    discard <| store `positive full (← mkAppM ``And.left #[spec])
                    discard <| store `continuation full (← mkAppM ``And.right #[spec])
                    traceStage s!"actual original comparison constants: {full.size} before-history inputs; SAME measurement/five budgets, original masks and common cutoff"

elab "cache_original_corrected_comparison_budgets" : command =>
  liftTermElabM (liftM cacheActualComparison)

end JanetCartan.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
