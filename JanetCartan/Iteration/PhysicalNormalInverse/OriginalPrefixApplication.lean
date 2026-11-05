module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalCarriers
public import JanetCartan.Iteration.PhysicalSampling.OriginalWeights
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicHighPass
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.OriginalCarrierPrefix
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity
public meta import Lean

/-!
# The actual original leading carrier-prefix application

The public zero-endpoint consumer keeps the entire already-supplied native
inverse predicate, but its normal is the measured carrier prefix, not the full
augmented inverse normal. The original a-prime mass, common mu, original angular
mask and one sampler rho are unchanged. No high-density Ar, profile51, Graw or
Cresp success premise is introduced. The actual qualitative leading matrix is
produced from the native C15 density certificate and retained LeadingCell facts.

The exact original dimension expression is reused throughout; in particular,
the native compatibility proof is applied directly instead of normalizing a
separate Nat.succ presentation of the large chosen original data.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse.OriginalPrefix
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier CanonicalConic
open CommonMeasurement NormalizedMeasurement Sampling SeparatedSampling
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open RawPrimary.MaskProfiles
open NullTransport ActualFlow FlowAmplitude AmplitudeBound

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q-fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (φ y : ℝ × (Euclidean (n-1) × Euclidean 3) → Euclidean (n-1) × Euclidean 3)
  (initial : Euclidean (n-1) × Euclidean 3 → ℝ)
  {μ a' r : ℝ} (hμ : 0 < μ) (hμcell : 4*μ < 1/2)
  (ha' : 0 < a') (hacell : 4*a' < 1/2)
  (z₀ : Euclidean 3) {ηb : Euclidean (n-1)} (hηb : ηb ≠ 0) (hr : 0 < r)

/-- The common measurement changes only the physical output cutoff: the original a-prime mass and angular mask are unchanged (`app:ch_background:defn:bg-row`). -/
theorem original_weight_common_data :
    commonChartData (data T Q F row col φ y initial ha' hacell
      (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr).1)
      FixedCutoffs.highFrequency) (closedBall 0 (4*μ)) (FixedCutoffs.periodic hμ hμcell 1) =
      data T Q F row col φ y initial hμ hμcell
        (fun z θ ↦ Real.sqrt (originalConicCarrierWeight z₀ ha' (carrierSamplingEquiv z)) *
          directionMask (NormedSpace.normalize ηb) (angularWidth_spec hηb hr).1 θ)
        FixedCutoffs.highFrequency := by
  rw [commonChartData_canonicalData]
  congr 1
  funext z θ
  exact (originalConicCarrierWeight_sqrt_mul_direction z₀ ha' hηb hr z θ).symm

/-- Transfer the SAME measured carrier adjoint to the original a-prime weighted data (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem original_weight_common_adjoint
    (carrier : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hadjoint : ∀ w, carrier.adjoint w =ᵐ[carrierMeasure n]
      carrierAdjointIntegral (commonChartData (data T Q F row col φ y initial ha' hacell
        (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr).1)
        FixedCutoffs.highFrequency) (closedBall 0 (4*μ))
        (FixedCutoffs.periodic hμ hμcell 1)) w) :
    ∀ w, carrier.adjoint w =ᵐ[carrierMeasure n]
      carrierAdjointIntegral (data T Q F row col φ y initial hμ hμcell
        (fun z θ ↦ Real.sqrt (originalConicCarrierWeight z₀ ha' (carrierSamplingEquiv z)) *
          directionMask (NormedSpace.normalize ηb) (angularWidth_spec hηb hr).1 θ)
        FixedCutoffs.highFrequency) w := by
  intro w
  rw [← original_weight_common_data T Q F row col φ y initial hμ hμcell ha' hacell z₀ hηb hr]
  exact hadjoint w

omit Q F row col φ y initial hμcell hacell hηb hr in
 /-- The common physical support and original carrier weight stay in the actual compatibility window (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem coordinates_of_original_weight
    {V : Set (ℝ × (Euclidean (n-1) × Euclidean 3))}
    (hcoords : MapsTo (densityCoordinates T)
      (closedBall (0 : Euclidean n) (6*μ) ×ˢ carrierSupport z₀ (r := a')) V)
    (x : Torus n) (hx : FixedCutoffs.physical hμ 1 (centeredTorusRepresentative x) ≠ 0)
    (z : CarrierParameter) (hz : originalConicCarrierWeight z₀ ha' (carrierSamplingEquiv z) ≠ 0) :
    coordinates (adaptedCoordinates T.data.adapted) (centeredTorusRepresentative x, parameter z) ∈ V := by
  have hz' : z ∈ carrierSupport z₀ (r := a') := by
    simpa only [carrierSamplingEquiv.symm_apply_apply] using originalConicCarrierWeight_support z₀ ha' hz
  exact hcoords (x := (centeredTorusRepresentative x,z))
    ⟨(closedBall_subset_closedBall (by linarith : 4*μ ≤ 6*μ))
      (FixedCutoffs.physical_tsupport_four hμ 1 (subset_tsupport _ hx)), hz'⟩

omit T Q F row col φ y initial hμcell hacell hηb hr in
 /-- The common physical cutoff lies on the original physical plateau (`app:ch_background:defn:bg-row`). -/
theorem common_measurement_in_original_support (hma : 6*μ < a')
    {x : Euclidean n} (hx : FixedCutoffs.physical hμ 1 x ≠ 0) :
    x ∈ tsupport (FixedCutoffs.physical ha' 1 : Euclidean n → ℝ) := by
  have he := physical_measurement_mul hμ ha' (by linarith : 3*μ ≤ 2*a') x
  have hone : FixedCutoffs.physical ha' 1 x = 1 := (mul_eq_left₀ hx).mp he
  exact subset_tsupport _ (by
    change FixedCutoffs.physical ha' 1 x ≠ 0
    rw [hone]
    exact one_ne_zero)

omit Q F row col φ y initial hμ hμcell hacell hηb hr in
 /-- The original mass stays on the one retained sampler graph (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem graph_of_original_weight {ρ : ℝ}
    (hgraph : ∀ z ∈ carrierSupport z₀ (r := a'),
      (parameter z,T.reference.spatialPatch (parameter z)) ∈
        closedBall (z₀,T.reference.spatialPatch z₀) (ρ/4)) :
    ∀ z : CarrierParameter, originalConicCarrierWeight z₀ ha' (carrierSamplingEquiv z) ≠ 0 →
      (parameter z,T.reference.spatialPatch (parameter z)) ∈
        closedBall (z₀,T.reference.spatialPatch z₀) (ρ/4) := by
  intro z hz
  apply hgraph z
  simpa only [carrierSamplingEquiv.symm_apply_apply] using originalConicCarrierWeight_support z₀ ha' hz

omit Q F row col φ y initial hμcell hacell hηb hr in
 /-- Use the actual joint-cutoff plateau at zero shift, without a second radius (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem zero_shift_original_plateau {ρ : ℝ} (hρ : 0 < ρ) (hma : 6*μ < a')
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (hκ : ∀ j : Fin 3, ∀ x ∈ tsupport (FixedCutoffs.physical ha' j : Euclidean n → ℝ),
      ∀ z ∈ carrierSupport z₀ (r := a'), ∀ shift : Euclidean (n-1), ‖shift‖ ≤ ρ/4 →
        κ (x,parameter z,T.reference.spatialPatch (parameter z)+shift) = 1)
    (x : Euclidean n) (hx : FixedCutoffs.physical hμ 1 x ≠ 0)
    (z : CarrierParameter) (hz : originalConicCarrierWeight z₀ ha' (carrierSamplingEquiv z) ≠ 0) :
    κ (x,parameter z,T.reference.spatialPatch (parameter z)) = 1 := by
  have hx' := common_measurement_in_original_support hμ ha' hma hx
  have hz' : z ∈ carrierSupport z₀ (r := a') := by
    simpa only [carrierSamplingEquiv.symm_apply_apply] using originalConicCarrierWeight_support z₀ ha' hz
  have hzero : ‖(0 : Euclidean (n-1))‖ ≤ ρ/4 := by rw [norm_zero]; positivity
  simpa only [add_zero] using hκ 1 x hx' z hz' 0 hzero

/-- The actual angular detector and fixed high-pass combine continuously at the origin (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sampling_detector_continuous {d : ℕ}
    {η : Euclidean (d-1)} {r : ℝ} (hη : η ≠ 0) (hr : 0 < r) :
    Continuous (detectorMask (originalConicDetector hη hr) (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖)) :=
  (contDiff_detectorMask (originalConicDetector hη hr)
    (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖)
    (fun _ hξ ↦ originalConicDetector_contDiffAt hη hr hξ)
    (contDiff_originalConicHighPass d)
    (fun _ hξ ↦ FixedCutoffs.highFrequency_zero hξ)).continuous

/-- The literal supported physical projection inherits the retained sampler radius (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem support_projection_of_tsupport {d : ℕ}
    {κ : Euclidean d × (Euclidean 3 × Euclidean (d-1)) → ℝ}
    {a : Euclidean d} {ρ : ℝ}
    (hs : Prod.fst '' tsupport κ ⊆ closedBall a (ρ/2)) :
    Prod.fst '' Function.support κ ⊆ closedBall a (ρ/2) := by
  rintro _ ⟨w,hw,rfl⟩
  exact hs ⟨w,subset_tsupport κ hw,rfl⟩

/-- The common measurement fits in the original source chart (`app:ch_background:defn:bg-row`). -/
theorem common_measurement_ball_inside {d : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {O : Set (Euclidean d)} (hO : closedBall (0 : Euclidean d) (6*μ) ⊆ O) :
    closedBall (0 : Euclidean d) (4*μ) ⊆ O :=
  (closedBall_subset_closedBall (by linarith : 4*μ ≤ 6*μ)).trans hO

end JanetCartan.PhysicalNormalInverse.OriginalPrefix

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse.OriginalPrefix
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation CorrectedAtoms
open ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement NormalizedMeasurement
open Sampling SeparatedSampling FullPhaseCharts PhysicalSampling

/-- Qualitative leading-matrix continuity from the scalar transport, with no high-profile or response premise (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supported_leading_principal_continuous
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q-fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ)
    {O : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hO : IsOpen O) (hspace : ∀ w ∈ O, w.1 ∈ U) (hdomain : O ⊆ domain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) O)
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hs : tsupport κ ⊆ O) :
    Continuous (fun w ↦ κ w • RawPrimary.fullLeadingPrincipalMatrix T Q F row col Φ Y r w) := by
  have hm := contDiffOn_retainedLeadingPrincipalMatrix T Q F row col Φ Y r
    hO hspace hdomain hF hi hrank hα
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w ∈ tsupport κ
  · exact hκ.continuous.continuousAt.smul (hm.continuousOn.continuousAt (hO.mem_nhds (hs hw)))
  · apply (continuousAt_const (y := (0 : Matrix (Fin N) (Fin n) ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport κ).isOpen_compl.mem_nhds hw] with z hz
    simp only [image_eq_zero_of_notMem_tsupport hz, zero_smul]

/-- Extend the actual locally smooth field using its original supported cutoff (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supported_field_smooth
    {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set X} (hO : IsOpen O) {κ : X → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ O) {f : X → E} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun p ↦ κ p • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport κ
  · exact hκ.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds (hs hp)))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport κ).isOpen_compl.mem_nhds hp] with q hq
    simp only [image_eq_zero_of_notMem_tsupport hq, zero_smul]

/-- One original sampler window sits inside the SAME retained full-flow domain (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem support_on_original_window {n : ℕ}
    {a b : Euclidean n × (Euclidean 3 × Euclidean (n-1))} {ρ σ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) {κ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ}
    (hκ : tsupport κ ⊆ closedBall b ρ)
    (hsmall : closedBall b (2*ρ) ⊆ ball a σ) {O : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hO : closedBall a (2*σ) ⊆ O) : tsupport κ ⊆ O :=
  hκ.trans ((closedBall_subset_closedBall (by linarith : ρ ≤ 2*ρ)).trans
    (hsmall.trans (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith : σ ≤ 2*σ)).trans hO))))

end JanetCartan.PhysicalNormalInverse.OriginalPrefix


end

public meta section
open Lean Meta Elab Command Term
namespace JanetCartan.PhysicalNormalInverse.OriginalPrefixApplication
private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do
    let type ← whnf (← inferType proof)
    unless type.isAppOfArity ``And 2 do throwError "non-conjunction at component {index}"
    proof := mkAppN (mkConst ``And.right) (type.getAppArgs.push proof)
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then
    return mkAppN (mkConst ``And.left) (type.getAppArgs.push proof)
  else pure proof

private def getArg (app : Expr) (key : Name) : MetaM Expr := do
  forallBoundedTelescope (← getConstInfo app.getAppFn.constName!).type (some app.getAppNumArgs) fun xs _ => do
    for i in [:xs.size] do
      if (← getFVarLocalDecl xs[i]!).userName == key then return app.getAppArgs[i]!
    throwError "missing argument {key} in {app.getAppFn}"

private def retainedArgs (params : Array Expr) : MetaM (Array Expr) := do
  let mut value := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.current) params
  for _ in [:4] do
    if value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current then break
    let some body := (← getConstInfo value.getAppFn.constName!).value?
      | throwError "original prefix: current alias lacks body"
    value := body.beta value.getAppArgs
  unless value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current && value.getAppNumArgs == 36 do
    throwError "original prefix: changed actual retained36"
  return value.getAppArgs

/-- Instantiate the zero-epsilon continuum prefix on the SAME original native
carrier, deriving qualitative leading continuity from the actual C15 certificate.
All masks, weights, the common measurement and the one sampler radius are retained
(`app:ch_waves:eq:sampling-prefix-normal`). -/
elab "apply_actual_original_carrier_prefix" : command => liftTermElabM do
  let currentNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let originalNS := `JanetCartan.PhysicalSeed.OriginalBoundary
  let choicesNS := `JanetCartan.PhysicalSampling.OriginalChoices
  let source := currentNS ++ `continuation
  withLocalDeclD `m (mkConst ``Nat) fun m => do
    let cutoffInfo ← getConstInfo (choicesNS ++ `Cutoff.κ)
    let afterM := cutoffInfo.type.bindingBody!.instantiate1 m
    let hnType := afterM.bindingBody!.bindingDomain!
    let n := hnType.getAppArgs.back!
    if n.hasLooseBVars then throwError "sampling dimension unexpectedly depends on order"
    forallBoundedTelescope (← inferType (mkApp (mkConst source) n)) (some 20) fun fixed _ => do
      unless fixed.size == 20 do throwError "missing original20"
      withLocalDeclD `pOrder (mkConst ``Nat) fun pOrder => do
        let hn := fixed[0]!
        let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra) #[m,hn,pOrder,fixed[19]!]
        let base := (#[n] ++ fixed).set! 20 merged
        let actual := mkAppN (mkConst source) base
        forallBoundedTelescope (← inferType actual) (some 23) fun tail _ => do
          unless tail.size == 23 do throwError "missing actual native44 tail"
          let all := base ++ tail
          let native := mkAppN (mkConst source) all
          let nt ← whnf (← inferType native)
          unless nt.isAppOfArity ``Exists 2 do throwError "missing entire native inverse predicate"
          withLocalDeclD `Vop nt.getAppArgs[0]! fun Vop => do
            withLocalDeclD `hNative (nt.appArg!.beta #[Vop]) fun hNative => do
              let vt ← whnf (← inferType Vop)
              withLocalDeclD `i vt.bindingDomain! fun i => do
                let publicParams := #[m,pOrder] ++ fixed ++ tail ++ #[i]
                let checkpoint (name : Name) (value : Expr) : MetaM Expr := do
                  let value ← instantiateMVars value
                  let resultType ← instantiateMVars (← inferType value)
                  let mut used := Lean.collectFVars (Lean.collectFVars {} resultType) value
                  for p in publicParams.reverse do
                    if used.fvarSet.contains p.fvarId! then
                      used := Lean.collectFVars used (← inferType p)
                  let params := publicParams.filter fun p ↦ used.fvarSet.contains p.fvarId!
                  let ty ← instantiateMVars (← mkForallFVars params resultType)
                  let va ← instantiateMVars (← mkLambdaFVars params value)
                  if ty.hasFVar || ty.hasMVar || ty.hasLevelMVar || va.hasFVar || va.hasMVar || va.hasLevelMVar then
                    throwError "incomplete checkpoint {name}"
                  let name := `JanetCartan.PhysicalNormalInverse.OriginalPrefix ++ name
                  let pair := Lean.ShareCommon.shareCommon (ty,va)
                  addDecl (.thmDecl { name, levelParams := [], type := pair.1, value := pair.2 }) (forceExpose := true)
                  return mkAppN (mkConst name) params
                let actualCurrent := all[:37].toArray.push i
                let args ← retainedArgs actualCurrent
                let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,merged]
                let selected := base.set! 20 capped
                let field (key : Name) := mkAppN (mkConst (selectedNS ++ key)) selected
                let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
                let l ← mkAppM ``Sigma.snd #[i]
                let cell := args[35]!
                let hroot ← mkAppM ``And.right #[mkAppN (field `fact1) #[q,l]]
                let samplerArgs := #[m,pOrder,hn,q,l,cell,hroot]
                let choice (part key : Name) := mkAppN (mkConst (choicesNS ++ part ++ key)) samplerArgs
                let radiusArgs := #[n,hn,q,l,cell]
                let radius := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius) radiusArgs
                let hRadius ← mkAppM ``Subtype.property #[radius]
                let spec := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius_spec) (radiusArgs.push hroot)
                let geometry := mkAppN (mkConst (currentNS ++ `geometry)) actualCurrent
                let patch := args[4]!.getAppArgs.back!
                let positive := mkAppN (mkConst (originalNS ++ `comparison_pos)) #[n,hn,patch,cell]
                let hWhole := choice `Cutoff `hκ_support
                let hSmall ← component spec 0
                let hOld ← component geometry 3
                let hSigma ← component positive 8
                let kb := (← inferType hWhole).getAppArgs.back!
                let oldArgs := (← inferType hOld).getAppArgs
                let oldBall := oldArgs[oldArgs.size-2]!
                let kbArgs := kb.getAppArgs
                let oldBallArgs := oldBall.getAppArgs
                let sig := (← inferType hSigma).getAppArgs.back!
                let support := mkAppN
                  (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.support_on_original_window)
                  #[n,oldBallArgs[oldBallArgs.size-2]!,kbArgs[kbArgs.size-2]!,kbArgs.back!,sig,
                    hRadius,hSigma,choice `Cutoff `κ,hWhole,hSmall,oldArgs.back!,hOld]
                let support ← checkpoint `support support
                logInfo "SAME actual original radius/cutoff support contained in SAME current O"
                let common := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.OriginalCarriers.common_measurement_of_native)
                  (all ++ #[Vop,hNative,i])
                let adjoint ← component common 11
                let originalRepresentations ← mkAppM ``And.left #[hNative]
                let representation := mkApp originalRepresentations i
                let rawAdjoint ← mkAppM ``And.right #[representation]
                forallBoundedTelescope (← inferType rawAdjoint) (some 1) fun ws _ => do
                  let mem ← mkAppM ``And.left #[mkApp rawAdjoint ws[0]!]
                  let some integral := (← inferType mem).find? (fun e ↦ e.isAppOf `JanetCartan.ContinuumRow.carrierAdjointIntegral)
                    | throwError "missing actual carrier data"
                  let d := (← getArg integral `d).headBeta
                  let initial ← getArg d `initial
                  logInfo m!"Actual carrier datum head {d.getAppFn}, initial head {initial.getAppFn}"
                  let cont := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.continuation) args
                  let initialDomain ← forallBoundedTelescope (← inferType cont) (some 1) fun _ tail => do
                    pure tail.bindingDomain!.getAppArgs.back!
                  let domainArgs := initialDomain.getAppArgs
                  let center := domainArgs[domainArgs.size-2]!
                  let scalar := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact6)
                    (base ++ #[center,mkApp args[10]! cell,← component positive 1,
                      all[21]!,← mkAppM ``And.left #[all[22]!],mkApp all[39]! i])
                  let lowerNorm (hHigh : Expr) (order : Nat) : TermElabM Expr := do
                    let highType ← inferType hHigh
                    let highArgs := highType.getAppArgs
                    let high := highArgs[highArgs.size-2]!
                    let normArgs := high.getAppArgs
                    unless high.getAppFn.isConstOf ``JanetCartan.cNorm do
                      throwError "expected actual cNorm source bound"
                    let highOrder := normArgs[normArgs.size-2]!
                    let lowOrder := mkNatLit order
                    let orderType ← mkAppM ``LE.le #[lowOrder,highOrder]
                    let hOrder ← Term.elabTermEnsuringType (← `(by omega)) orderType
                    Term.synthesizeSyntheticMVarsNoPostponing
                    let monoInfo ← getConstInfo ``JanetCartan.cNorm_mono_order
                    let mono := mkAppN (mkConst ``JanetCartan.cNorm_mono_order
                      (monoInfo.levelParams.map fun _ ↦ Level.zero))
                      (normArgs[:normArgs.size-2].toArray ++ #[lowOrder,highOrder,normArgs.back!,hOrder])
                    let result ← mkAppM `le_trans #[mono,hHigh]
                    pure result
                  let hDensity15 ← lowerNorm (mkApp all[43]! i) 15
                  let low := mkAppN scalar #[mkApp all[40]! i,mkApp all[41]! i,mkApp all[42]! i,hDensity15]
                  let low ← checkpoint `scalar_admission low
                  let hInitial ← component low 0
                  let hInitial14 ← lowerNorm (← component low 1) 14
                  let hLower ← component low 2
                  let solution := mkAppN cont #[initial,hInitial,hInitial14,hLower]
                  let hAlpha ← component solution 0
                  let hAlpha ← checkpoint `scalar_regularity hAlpha
                  let T := args[4]!
                  let Q := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingData.Q) args[:35].toArray
                  let F := args[30]!
                  let row := mkApp args[7]! cell
                  let col := mkApp args[8]! cell
                  let Phi := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.Φ) args
                  let Y := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.Y) args
                  let hA := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.supported_leading_principal_continuous)
                    #[n,← getArg d `N,← getArg d `P,← getArg d `U,← getArg d `hU,
                      T,Q,F,row,col,Phi,Y,initial,(← inferType hAlpha).getAppArgs.back!,
                      ← component geometry 0,← component geometry 1,← component geometry 2,
                      args[31]!,args[32]!,args[33]!,hAlpha,
                      choice `Cutoff `κ,choice `Cutoff `hκ,support]
                  let hAArgs := hA.getAppArgs
                  let mut hAFunction := hA.getAppFn
                  for argIndex in [:hAArgs.size] do
                    let argType ← whnf (← inferType hAFunction)
                    unless argType.isForall do throwError "hA application overapplied at {argIndex}"
                    let actualType ← inferType hAArgs[argIndex]!
                    unless ← isDefEq argType.bindingDomain! actualType do
                      throwError "hA[{argIndex}] {argType.bindingName!} has wrong type\nEXPECTED {argType.bindingDomain!}\nACTUAL {actualType}"
                    hAFunction := mkApp hAFunction hAArgs[argIndex]!
                  let hMatrix := mkAppN
                    (mkConst `JanetCartan.CorrectedAtoms.contDiffOn_retainedLeadingPrincipalMatrix)
                    hA.getAppArgs[:21].toArray
                  let hMatrix ← checkpoint `local_leading_matrix hMatrix
                  let hSmooth ← mkAppM `JanetCartan.PhysicalNormalInverse.OriginalPrefix.supported_field_smooth
                    #[← component geometry 0,choice `Cutoff `hκ,support,hMatrix]
                  let hSmooth ← checkpoint `native_leading_smooth hSmooth
                  let smoothType ← inferType hSmooth
                  let continuousInfo ← getConstInfo ``ContDiff.continuous
                  let hA ← forallTelescope continuousInfo.type fun xs _ => do
                    let proof := xs.back!
                    let formal := (← inferType proof).getAppArgs
                    let actual := smoothType.getAppArgs
                    unless formal.size == actual.size do throwError "ContDiff application shape changed"
                    let mut values : Array Expr := #[]
                    for x in xs.pop do
                      let some j := formal.findIdx? (· == x)
                        | throwError "continuity parameter absent from exact smoothness predicate: {(← getFVarLocalDecl x).userName}"
                      values := values.push actual[j]!
                    pure (mkAppN (mkConst ``ContDiff.continuous
                      (continuousInfo.levelParams.map fun _ ↦ Level.zero)) (values.push hSmooth))
                  let hAStored ← checkpoint `native_leading_continuity hA
                  let _ := hAStored
                  logInfo "Kernel-checked original44 plus sampling order: actual leading continuity, no profile or inverse success premise"
                  -- SAME ORIGINAL ZERO-ENDPOINT APPLICATION: inserted after native hA0.
                  let hA := hAStored
                  let da := d.getAppArgs
                  let hcompat := mkAppN (mkConst (currentNS ++ `compatible))
                    (actualCurrent.push initial)
                  let fullAmplitude ← forallBoundedTelescope (← inferType hcompat) (some 2) fun _ result => do
                    let result ← whnf result
                    unless result.isAppOfArity ``Eq 3 do throwError "original compatibility endpoint changed"
                    let lhs := result.getAppArgs[1]!
                    unless lhs.isAppOf `JanetCartan.LeadingWave.FullModulation.scalarAmplitude do
                      throwError "original compatibility lacks its literal full amplitude"
                    pure lhs
                  let T ← getArg fullAmplitude `T
                  let Q ← getArg fullAmplitude `Q
                  let F ← getArg fullAmplitude `F
                  let row ← getArg fullAmplitude `row
                  let col ← getArg fullAmplitude `col
                  let phi := da[10]!.headBeta
                  let y := da[11]!.headBeta
                  let Phi ← getArg fullAmplitude `Φ
                  let Y ← getArg fullAmplitude `Y
                  let hmu := field `hrMeasure
                  let hmucell := field `hMeasureCell
                  let mu := field `rMeasure
                  let ha := da[14]!
                  let hacell := da[15]!
                  let angular := da[16]!.headBeta
                  unless angular.isAppOf `JanetCartan.ContinuumRow.CanonicalConic.angularMask do
                    throwError "native original angular mask changed"
                  let zRoot ← getArg angular `z₀
                  let widthProof ← getArg angular `ha
                  let aw := widthProof.getAppArgs.back!.headBeta
                  unless aw.isAppOf `JanetCartan.ContinuumRow.CanonicalConic.angularWidth_spec do
                    throwError "original angular-width certificate changed: {aw.getAppFn}"
                  let hEta ← getArg aw `hηb
                  let hr ← getArg aw `hr
                  let theta ← getArg angular `θ₀
                  let angleBump := mkAppN (mkConst `JanetCartan.ContinuumRow.CanonicalConic.directionMask)
                    #[n,theta,← getArg angular `a,widthProof]
                  let angle ← mkAppM ``ContDiffBump.toFun #[angleBump]
                  let weightsArgs := #[m,hn,pOrder] ++ fixed[1:].toArray
                  let weight (key : Name) := mkAppN
                    (mkConst (`JanetCartan.PhysicalSampling.OriginalWeights ++ key)) weightsArgs
                  let psi := mkApp (weight `φ) i
                  let hpsi := mkApp (weight `patchBounds) i
                  let hpsic ← mkAppM ``ContDiff.continuous #[mkApp (weight `smooth) i]
                  let admission := mkAppN
                    (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row)
                    (weightsArgs.push i)
                  let rho := (← inferType hRadius).getAppArgs.back!
                  let aPrime := da[13]!
                  let hgraph := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.graph_of_original_weight)
                    #[n,da[1]!,da[2]!,da[3]!,T,aPrime,ha,zRoot,rho,← component admission 3]
                  let hPlateau := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.zero_shift_original_plateau)
                    #[n,da[1]!,da[2]!,da[3]!,T,mu,aPrime,hmu,ha,zRoot,rho,hRadius,
                      mkApp (field `fact60) i,choice `Cutoff `κ,← component admission 4]
                  let coords := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalCarriers.common_measurement_coordinates)
                    actualCurrent
                  let hcoords := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.coordinates_of_original_weight)
                    #[n,da[1]!,da[2]!,da[3]!,T,mu,aPrime,hmu,ha,zRoot,
                      (← inferType coords).getAppArgs.back!,coords]
                  let hKappa ← mkAppM
                    `JanetCartan.PhysicalNormalInverse.OriginalPrefix.support_projection_of_tsupport
                    #[choice `Cutoff `hκ_radius]
                  let hSource := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalMeasurement.source_ball_inside_original_chart)
                    all[:31].toArray
                  let hBall ← mkAppM
                    `JanetCartan.PhysicalNormalInverse.OriginalPrefix.common_measurement_ball_inside #[hmu,hSource]
                  let eta ← getArg aw `ηb
                  let rMask ← getArg aw `r
                  let detectorArgs := #[n,eta,rMask,hEta,hr]
                  let hdetector := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.sampling_detector_continuous) detectorArgs
                  let hdetBound := mkAppN (mkConst `JanetCartan.Sampling.norm_originalConicDetectorMask_le_one) detectorArgs
                  let commonAdjoint ← forallBoundedTelescope (← inferType adjoint) (some 1) fun qs _ => do
                    mkLambdaFVars qs (← component (mkAppN adjoint qs) 1)
                  let V ← forallBoundedTelescope (← inferType commonAdjoint) (some 1) fun _ result => do
                    let some V := result.find? (fun e ↦ e.isAppOf
                      `JanetCartan.ContinuumRow.CommonMeasurement.restrictCarrier)
                      | throwError "SAME native measured carrier missing in adjoint"
                    if V.hasLooseBVars then throwError "measured carrier depends on adjoint test"
                    pure V
                  let hAdjoint := mkAppN
                    (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.original_weight_common_adjoint)
                    #[n,da[6]!,da[1]!,da[2]!,da[3]!,T,Q,F,row,col,phi,y,initial,
                      mu,aPrime,rMask,hmu,hmucell,ha,hacell,zRoot,eta,hEta,hr,V,commonAdjoint]
                  let hPhase ← component spec 1
                  let phaseArgs := (← inferType hPhase).getAppArgs
                  let graphBall := phaseArgs[phaseArgs.size-2]!
                  let graphArgs := graphBall.getAppArgs
                  let a := graphArgs[graphArgs.size-2]!
                  let haz ← mkAppM ``Eq.refl #[zRoot]
                  let patchFacts ← component (mkAppN (mkConst (originalNS ++ `hD)) #[n,hn]) 4
                  let chart ← mkAppM ``Prod.fst #[← mkAppM ``Subtype.val #[q]]
                  let hP ← mkAppM ``And.left #[mkAppN patchFacts #[chart,l]]
                  let pArgs := (← inferType hP).getAppArgs
                  let compatType ← whnf (← inferType hcompat)
                  let Vcomp ← forallBoundedTelescope compatType (some 1) fun _ rest => do
                    let membership := rest.bindingDomain!.getAppArgs
                    pure membership[membership.size-2]!
                  let generic := `JanetCartan.Sampling.CorrectedTransport.leadingCrossTransportPrefix_normal_eq_original
                  let genericInfo ← getConstInfo generic
                  withLocalDeclD `J (mkConst ``Nat) fun J => do
                    withLocalDeclD `cutoff (mkConst ``Real) fun cutoff => do
                      let count := mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) cutoff
                      let hLType ← mkAppM ``LE.le #[count,J]
                      withLocalDeclD `hL hLType fun hL => do
                        let one ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real),some (mkNatLit 1),none]
                        let hOne ← Term.elabTerm (← `((show (0 : ℝ) ≤ 1 from zero_le_one))) none
                        Term.synthesizeSyntheticMVarsNoPostponing
                        let hhigh := Lean.mkConst `JanetCartan.ContinuumRow.FixedCutoffs.highFrequency_zero
                        let values : Array (Name × Expr) := #[
                          (`m,m),(`N,da[6]!),(`J,J),(`P,da[1]!),(`U,da[2]!),(`hU,da[3]!),
                          (`T,T),(`Q,Q),(`F,F),(`row,row),(`col,col),(`Φ,Phi),(`Y,Y),(`r,initial),
                          (`κ,choice `Cutoff `κ),(`z₀,zRoot),(`ρ,← mkAppM ``Subtype.val #[radius]),
                          (`hρ,hRadius),(`hκc,choice `Cutoff `hκ_compact),(`hA₀,hA),
                          (`c₀,pArgs[pArgs.size-2]!),(`C₀,pArgs.back!),(`hP,hP),(`V,Vcomp),
                          (`hcarrier,← component spec 3),(`φ,phi),(`y,y),(`hcompat,hcompat),
                          (`b,mu),(`hb,hmu),(`hbcell,hmucell),(`hball,hBall),(`angle,angle),
                          (`high,da[17]!),(`hd,hdetector),(`Md,one),(`hMd,hOne),(`hdb,hdetBound),
                          (`ψ,psi),(`a,a),(`haz,haz),(`hphase,hPhase),(`hκ,hKappa),
                          (`hψgraph,hgraph),(`hκone,hPlateau),(`hcoords,hcoords),
                          (`Bψ,weight `B),(`Pψ,one),(`hψ,hpsi),(`hψc,hpsic),(`hhigh,hhigh),
                          (`carrier,V),(`hadjoint,hAdjoint),(`cutoff,cutoff),(`hL,hL)]
                        let application ← forallTelescope genericInfo.type fun xs _ => do
                          let mut actualArgs : Array Expr := #[]
                          for x in xs do
                            let key := (← getFVarLocalDecl x).userName
                            let some entry := values.find? (fun p ↦ p.1 == key)
                              | throwError "unassigned original prefix argument {key}"
                            actualArgs := actualArgs.push entry.2
                          let mut f : Expr := Lean.mkConst generic
                          for j in [:actualArgs.size] do
                            let fType ← whnf (← inferType f)
                            let actualTy ← inferType actualArgs[j]!
                            unless ← isDefEq fType.bindingDomain! actualTy do
                              throwError "original prefix argument {j} ({fType.bindingName!}) has wrong type"
                            f := mkApp f actualArgs[j]!
                          pure f
                        let result ← mkAppM ``And.intro #[hNative,application]
                        let parameters := publicParams.pop ++ #[Vop,hNative,i,J,cutoff,hL]
                        let type ← instantiateMVars (← mkForallFVars parameters (← inferType result))
                        let value ← instantiateMVars (← mkLambdaFVars parameters result)
                        if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then
                          let escaped := (Lean.collectFVars (Lean.collectFVars {} type) value).fvarIds
                          throwError "unclosed original zero-endpoint declaration: free={escaped.map FVarId.name}; typeMVar={type.hasMVar}; valueMVar={value.hasMVar}"
                        let name := `JanetCartan.PhysicalNormalInverse.OriginalPrefix.of_native
                        addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)

end JanetCartan.PhysicalNormalInverse.OriginalPrefixApplication

end
