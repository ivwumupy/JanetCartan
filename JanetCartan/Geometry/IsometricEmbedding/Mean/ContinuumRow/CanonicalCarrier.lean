module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualQuotient
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Adapted
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalNormal
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.SymbolBridge

/-!
# Literal carrier data from the retained Hamilton and null-transport families

The functions in `app:ch_background:defn:bg-carriers` and `app:ch_background:eq:bg-T`
use the SAME `PatchQuantitativeFamily.currentChart` and the literal positive
scalar `carrierScalarAmplitude`. In particular the transport phase uses the
covector derivative of the Hamilton phase, not the ODE footpoint function.

This leaf fixes the objects for the conic-chart and primitive-coefficient
instantiations of `exists_carrierL2Extension_globalNormal_of_primitiveNorms`.
It proves the phase identification and regularity, and identifies the normal
and reduced coefficients algebraically. Selection of the flow, buffered masks,
and their uniform estimates is still required by the full row construction.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open NullTransport LeadingWave AmbientResponse

/-- Reassemble the literal initial variables `(s,v)` into the retained
three-dimensional carrier label (`app:ch_background:defn:bg-carriers`). -/
def parameter : CarrierParameter →L[ℝ] Euclidean 3 :=
  carrierParameters.comp (ContinuousLinearEquiv.prodComm ℝ ℝ (Euclidean 2)).toContinuousLinearMap

@[simp] theorem parameter_apply (z : CarrierParameter) :
    parameter z = carrierParameters (z.2, z.1) := rfl

/-- The carrier labels are exactly the inverse of the existing canonical
Euclidean slice coordinates (`app:ch_background:defn:bg-carriers`). -/
theorem parameter_eq_sliceCoordinates_symm :
    (parameter : CarrierParameter → Euclidean 3) =
      (TransportKernel.sliceCoordinates 2).symm := by
  funext z
  apply (TransportKernel.sliceCoordinates 2).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

/-- The literal `(ds,dv)` measure is Euclidean volume in the retained carrier
labels; this is only a fixed coordinate relabeling, not transport by `Y`
(`app:ch_background:eq:bg-T`). -/
theorem parameter_measurePreserving :
    MeasureTheory.MeasurePreserving parameter
      (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume := by
  rw [show (parameter : CarrierParameter → Euclidean 3) =
    (TransportKernel.sliceCoordinates 2).symm from parameter_eq_sliceCoordinates_symm]
  exact (TransportKernel.sliceCoordinates_measurePreserving 2).symm
    (TransportKernel.sliceCoordinates 2)

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Orthogonal physical coordinates of the SAME Hamilton chart
(`app:ch_background:eq:bg-Psi`). -/
def physicalCoordinates : Euclidean n ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Euclidean (n - 1)) :=
  (LinearIsometryEquiv.ofSurjective (adaptedSpacetime T.data.adapted)
    (adaptedSpacetime_surjective T.data.adapted)).symm

/-- The physical map and the retained adapted chart are exact inverses
(`app:ch_background:defn:bg-carriers`). -/
@[simp] theorem physicalCoordinates_adapted (x : WithLp 2 (ℝ × Euclidean (n - 1))) :
    physicalCoordinates T (adaptedSpacetime T.data.adapted x) = x :=
  LinearIsometryEquiv.symm_apply_apply _ x

/-- Return to the original physical point without a dilation or translation
(`app:ch_background:defn:bg-carriers`). -/
@[simp] theorem adapted_physicalCoordinates (x : Euclidean n) :
    adaptedSpacetime T.data.adapted (physicalCoordinates T x) = x :=
  (LinearIsometryEquiv.ofSurjective (adaptedSpacetime T.data.adapted)
    (adaptedSpacetime_surjective T.data.adapted)).apply_symm_apply x

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The adapted phase evaluates the retained Hamilton chart at the original
physical point and zero energy (`app:ch_background:defn:bg-carriers`). -/
theorem current_physicalCoordinates (x : Euclidean n) (ζ : Euclidean (n - 1)) :
    ActualPhase.current T Q (physicalCoordinates T x, ζ) =
      HamiltonPhase.phase (T.currentChart Q).coordinates (x, (0, ζ)) := by
  simp only [ActualPhase.current, adaptedPhaseInclusion_apply, adapted_physicalCoordinates]

/-- The actual `Y = d_ζ S(x,ζ(z))` in `app:ch_background:defn:bg-carriers`.
The frequency convention is the physical radian covector, with no `2π` factor. -/
def transportPosition (p : Euclidean n × CarrierParameter) : Euclidean (n - 1) :=
  gradient (fun ζ ↦ ActualPhase.current T Q (physicalCoordinates T p.1, ζ))
    (T.reference.spatialPatch (parameter p.2))

/-- Literal `d_ζ S_G(x,ζ_a(z))` in the original physical coordinates,
identifying the function used by the row with the actual Hamilton producer
(`app:ch_background:defn:bg-carriers`). -/
theorem transportPosition_eq_hamiltonGradient (p : Euclidean n × CarrierParameter) :
    transportPosition T Q p =
      gradient (fun ζ ↦ HamiltonPhase.phase (T.currentChart Q).coordinates (p.1, (0, ζ)))
        (T.reference.spatialPatch (parameter p.2)) := by
  simp only [transportPosition, current_physicalCoordinates]

/-- The zero-shift full modulation is literally the carrier transport phase
(`app:ch_seed:eq:seed-quotient-integral`, `app:ch_background:eq:bg-Psi`). -/
theorem transportPosition_inner_eq_modulation (x : Euclidean n)
    (z : CarrierParameter) (η : Euclidean (n - 1)) :
    inner ℝ (transportPosition T Q (x, z)) η =
      ActualPhase.modulation T Q ((parameter z, η), 0) (physicalCoordinates T x) := by
  rw [ActualPhase.modulation_zero]
  exact inner_gradient_left

/-- The same identity in the precise coordinates of the released annular
full-phase chart (`app:ch_background:eq:bg-Psi`). -/
theorem transportPosition_inner_eq_comparison (x : Euclidean n)
    (z : CarrierParameter) (η : Euclidean (n - 1)) :
    inner ℝ (transportPosition T Q (x, z)) η =
      Comparison.modulationPhase (ActualPhase.current T Q) (ActualPhase.spatialCarrier T)
        0 z.2 (z.1, η) (physicalCoordinates T x) := by
  simp only [Comparison.modulationPhase, phaseShiftQuotient_zero,
    ActualPhase.spatialCarrier, transportPosition, parameter_apply]

/-- Joint smoothness of the actual transported position, on fixed physical
and carrier buffers. This discharges the qualitative `Y` input of the
carrier-symbol producer (`app:ch_background:eq:bg-mixed-input`). -/
theorem transportPosition_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (transportPosition T Q)
      (ball (0 : Euclidean n) T.family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * P.radius / 2))) := by
  let X := ball (0 : WithLp 2 (ℝ × Euclidean (n - 1))) T.family.radius
  let Z := ball (ActualPhase.covectorCenter T) T.family.radius
  have hS : ContDiffOn ℝ ∞ (ActualPhase.current T Q) (X ×ˢ Z) := by
    apply (ActualPhase.current_smooth T Q).mono
    intro q hq
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hq.1).trans (by linarith [T.family.radius_pos]),
      (mem_ball.mp hq.2).trans (by linarith [T.family.radius_pos])⟩
  have hg := contDiffOn_phaseGradient
    (S := fun x ζ ↦ ActualPhase.current T Q (x, ζ)) isOpen_ball isOpen_ball hS
  have hz : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T.reference.spatialPatch (parameter p.2))
      (ball (0 : Euclidean n) T.family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * P.radius / 2))) := by
    apply (T.reference.spatialPatch_smooth hP).comp
      (parameter.contDiff.contDiffOn.comp contDiffOn_snd (fun _ _ ↦ mem_univ _))
    intro p hp
    exact (ActualPhase.middle_parameter_buffers hP).2 (fun i ↦ (hp.2 i).le)
  apply hg.comp
    (((physicalCoordinates T).contDiff.contDiffOn.comp contDiffOn_fst
      (fun _ _ ↦ mem_univ _)).prodMk hz)
  intro p hp
  constructor
  · simpa only [X, Function.comp_apply, mem_ball, dist_zero_right,
      LinearIsometryEquiv.norm_map] using hp.1
  · obtain ⟨ε, hε, hshift⟩ := ActualPhase.exists_covector_shift_buffer T hP (by norm_num : (0 : ℝ) < 1)
    have hh := hshift (parameter p.2) (fun i ↦ (hp.2 i).le)
      0 (by simp) 0 (by simpa using hε.le) 0 (by constructor <;> norm_num)
    simpa only [zero_mul, zero_smul, add_zero] using hh

/-- The literal positive scalar, null column and canonical normal completion
give the normal field in `app:ch_background:eq:bg-T`. Flow maps are the maps
constructed by `exists_projected_local_positive_amplitude`; no normal-field
estimate or desired operator conclusion is a field of this definition. -/
def normalField {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (x : Euclidean n) (z : CarrierParameter) : Euclidean N :=
  principalNormal (canonicalNormalCompletion F x) (T.carrierGradient Q x (parameter z))
    (carrierScalarAmplitude T Q F row col Φ Y initial (x, parameter z) •
      carrierNullvector T Q col (x, parameter z))

/-- Actual function data for the continuum kernel, with the common physical
cutoff and the original Lebesgue initial variables (`app:ch_background:eq:bg-T`).
The angular cutoff is selected on the buffered conic chart separately. -/
def data {N : ℕ} (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    CarrierData n N where
  outputChart := PeriodicLocalL2.torusChart (closedBall 0 (4 * r))
  chartPoint := AmplitudeBound.centeredTorusRepresentative
  transportedPosition := fun x z ↦ transportPosition T Q (x, z)
  covector := fun x z ↦ T.carrierGradient Q x (parameter z)
  normalField := normalField T Q F row col Φ Y initial
  stressFrame := Q.1
  measurementCutoff := FixedCutoffs.periodic hr hcell 1
  angularCutoff := angular
  highCutoff := high

/-- Exact reduced detector for the canonical row, agreeing with the detector
used by actual incidence and Gram estimates (`app:ch_background:defn:bg-geometry`). -/
theorem reducedCovector_data {N : ℕ} (F : Euclidean n → Euclidean N)
    (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (x ξ : Euclidean n) :
    reducedCovector (data T Q F row col Φ Y initial hr hcell angular high) x ξ =
      ActualCarriers.quadratic (Q.1 x) ξ := by
  ext i
  change (∑ j, ∑ k, Q.1 x i j k * (ξ j * ξ k)) =
    ∑ j, ∑ k, ξ j * Q.1 x i j k * ξ k
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end JanetCartan.ContinuumRow.CanonicalCarrier
