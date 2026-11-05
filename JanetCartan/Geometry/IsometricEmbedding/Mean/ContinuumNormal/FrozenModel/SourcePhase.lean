module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.SmoothPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalPhase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ZeroEnergyBounds

/-!
# The zero-scale phase of the retained carrier

The first step of `new:lem:scaling` in the frozen-model argument of
`app:ch_background:prop:bg-frame`. These definitions use the zero-energy
restriction of the SAME Hamilton chart as `CanonicalCarrier.data`. The
canonical derivative at scale zero is proved to be linear in the physical
variable. No independent phase or frozen transport map is selected.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow.CanonicalCarrier NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The normalized phase uses the integral source extension of the actual
zero-energy phase (`new:lem:scaling`). -/
def normalizedPhase (σ : ℝ) (x : Euclidean n) (ζ : Euclidean (n - 1)) : ℝ :=
  sourcePhaseExtension (T.zeroEnergyPhase Q) (σ, (x, ζ))

/-- The physical covector of the SAME extended phase
(`app:ch_background:eq:bg-Nsigma`). -/
def normalizedCovector (σ : ℝ) (x : Euclidean n) (z : ContinuumRow.CarrierParameter) :
    Euclidean n :=
  gradient (fun y ↦ normalizedPhase T Q σ y (T.reference.spatialPatch (parameter z))) x

/-- The canonical derivative `Yσ = d_ζ Sσ`, with the original carrier labels
(`app:ch_background:defn:bg-carriers`). -/
def normalizedTransportPosition (σ : ℝ)
    (p : Euclidean n × ContinuumRow.CarrierParameter) : Euclidean (n - 1) :=
  gradient (normalizedPhase T Q σ p.1) (T.reference.spatialPatch (parameter p.2))

/-- The frozen covector is the actual seed covector at physical zero
(`new:lem:scaling`). -/
def seedCovector (ζ : Euclidean (n - 1)) : Euclidean n :=
  gradient (fun x ↦ T.zeroEnergyPhase Q (x, ζ)) 0

/-- Exact zero-scale source formula (`new:lem:scaling`). -/
theorem normalizedPhase_zero (x : Euclidean n) (ζ : Euclidean (n - 1)) :
    normalizedPhase T Q 0 x ζ = inner ℝ (seedCovector T Q ζ) x :=
  sourcePhaseExtension_zero _ _ _

/-- Spatial independence of the actual normalized phase covector
(`new:lem:scaling`); the remaining argument is the unchanged carrier label. -/
theorem normalizedCovector_zero (x : Euclidean n) (z : ContinuumRow.CarrierParameter) :
    normalizedCovector T Q 0 x z = seedCovector T Q (T.reference.spatialPatch (parameter z)) :=
  gradient_sourcePhaseExtension_position_zero _ _ _

/-- Smoothness of the retained zero-energy phase in physical coordinates.
This supplies the differentiation premise for `normalizedTransportPosition_zero`
in `new:lem:scaling`. -/
theorem zeroEnergyPhase_smooth :
    ContDiffOn ℝ ∞ (T.zeroEnergyPhase Q)
      (ball (0 : Euclidean n) T.family.radius ×ˢ
        ball (ActualPhase.covectorCenter T) T.family.radius) := by
  have he : T.zeroEnergyPhase Q = fun p ↦
      ActualPhase.current T Q (physicalCoordinates T p.1, p.2) := by
    funext p
    exact (current_physicalCoordinates T Q p.1 p.2).symm
  rw [he]
  apply (ActualPhase.current_smooth T Q).comp
    (((physicalCoordinates T).contDiff.contDiffOn.comp contDiffOn_fst
      (fun _ _ ↦ mem_univ _)).prodMk contDiffOn_snd)
  intro p hp
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [Function.comp_apply, dist_zero_right, LinearIsometryEquiv.norm_map] using
      (mem_ball.mp hp.1).trans (show T.family.radius < 2 * T.family.radius by
        linarith [T.family.radius_pos])
  · exact (mem_ball.mp hp.2).trans (by linarith [T.family.radius_pos])

/-- Smoothness of the actual frozen covector, derived from the Hamilton
phase instead of imposed on the frozen model (`new:lem:scaling`). -/
theorem seedCovector_smooth :
    ContDiffOn ℝ ∞ (seedCovector T Q)
      (ball (ActualPhase.covectorCenter T) T.family.radius) := by
  exact (contDiffOn_phase_positionGradient isOpen_ball isOpen_ball
    (zeroEnergyPhase_smooth T Q)).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ h ↦ ⟨by simpa using T.family.radius_pos, h⟩)

/-- The linear map whose application is `Y₀(x,z)` in `new:lem:scaling`.
It is the adjoint of the actual covector differential. -/
def frozenTransportLinearMap (z : ContinuumRow.CarrierParameter) :
    Euclidean n →L[ℝ] Euclidean (n - 1) :=
  (fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch (parameter z))).adjoint

omit Q in
/-- The constructed spatial patch supplies the domain premise in
`normalizedTransportPosition_zero`, on the retained carrier buffer
(`new:lem:scaling`, `app:ch_seed:prop:seed-phase-charts`). -/
theorem spatialPatch_mem_phaseBuffer {c C : ℝ} (hP : P.IsValid c C)
    {z : ContinuumRow.CarrierParameter}
    (hz : parameter z ∈ parameterCube (3 * P.radius / 2)) :
    T.reference.spatialPatch (parameter z) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius := by
  obtain ⟨ε, hε, hb⟩ := ActualPhase.exists_covector_shift_buffer T hP
    (by norm_num : (0 : ℝ) < 1)
  simpa using hb (parameter z) hz 0 (by simp) 0 (by simpa using hε.le)
    0 (by constructor <;> norm_num)

/-- Identification of the zero-scale canonical derivative with its linear
map. The only domain hypothesis is membership in the seed phase buffer
(`new:lem:scaling`). -/
theorem normalizedTransportPosition_zero {z : ContinuumRow.CarrierParameter}
    (hz : T.reference.spatialPatch (parameter z) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius) (x : Euclidean n) :
    normalizedTransportPosition T Q 0 (x, z) = frozenTransportLinearMap T Q z x := by
  have hd := ((seedCovector_smooth T Q).contDiffAt
    (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have he : normalizedPhase T Q 0 x = fun ζ ↦ inner ℝ (seedCovector T Q ζ) x :=
    funext (normalizedPhase_zero T Q x)
  apply ext_inner_right ℝ
  intro η
  simp only [normalizedTransportPosition, he, inner_gradient_left,
    frozenTransportLinearMap, ContinuousLinearMap.adjoint_inner_left]
  rw [fderiv_inner_apply ℝ hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
  exact real_inner_comm _ _

/-- The literal frozen transport phase is a linear physical phase, with the
physical radian covector and no Fourier normalization inserted
(`app:ch_background:eq:bg-Psi`). -/
theorem normalizedTransportPhase_zero {z : ContinuumRow.CarrierParameter}
    (hz : T.reference.spatialPatch (parameter z) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius)
    (x : Euclidean n) (η : Euclidean (n - 1)) :
    inner ℝ (normalizedTransportPosition T Q 0 (x, z)) η =
      inner ℝ x (fderiv ℝ (seedCovector T Q)
        (T.reference.spatialPatch (parameter z)) η) := by
  rw [normalizedTransportPosition_zero T Q hz]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The averaged physical gradient loses both position variables at scale
zero, as required by the frozen normal kernel in
`app:ch_background:prop:bg-frame`. -/
theorem transportAveragedGradient_zero (p : InputVariables n)
    (hz : T.reference.spatialPatch (parameter p.2.1) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius) :
    transportAveragedGradient (normalizedTransportPosition T Q 0) p =
      fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch (parameter p.2.1)) p.2.2 := by
  have he : (fun x ↦ inner ℝ (normalizedTransportPosition T Q 0 (x, p.2.1)) p.2.2) =
      fun x ↦ inner ℝ
        (fderiv ℝ (seedCovector T Q) (T.reference.spatialPatch (parameter p.2.1)) p.2.2) x := by
    funext x
    rw [normalizedTransportPhase_zero T Q hz, real_inner_comm]
  have hg (v x : Euclidean n) : gradient (fun y ↦ inner ℝ v y) x = v :=
    ((InnerProductSpace.toDual ℝ (Euclidean n) v).hasFDerivAt.hasGradientAt.gradient).trans
      ((InnerProductSpace.toDual ℝ (Euclidean n)).symm_apply_apply v)
  simp only [transportAveragedGradient, he, hg, intervalIntegral.integral_const,
    sub_zero, one_smul]

end JanetCartan.ContinuumNormal.FrozenModel
