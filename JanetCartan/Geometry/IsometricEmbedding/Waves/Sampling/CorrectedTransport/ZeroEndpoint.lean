module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.CrossAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CompatibleTransportEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportAmplitude

/-!
# The squared-normal coefficient at the corrected transport endpoint

At zero interpolation parameter the original carrier insertion fixes both
principal matrices. Their real cutoffs multiply, and their measured cross
tensor is precisely the squared carrier normal on the SAME compatible flow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition
open CurrentMean NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
    Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)


/-- Real linearity in the unmasked background factor, retaining the literal
complex-linear second factor (`app:ch_mean_pairs:defn:mean-canonical`). -/
private theorem complexCrossMeasurement_real_smul_left {n N : ℕ}
    (C : MetricTensor n →L[ℝ] Euclidean n) (a : ℝ)
    (A : Matrix (Fin N) (Fin n) ℂ) :
    complexCrossMeasurement C (a • A) = a • complexCrossMeasurement C A := by
  ext V i
  change (euclideanComplexInclusion (C (hermitianContinuousBilinear (a • A) V)) -
      Complex.I • euclideanComplexInclusion
        (C (hermitianContinuousBilinear (a • A) (Complex.I • V)))) i =
    (a • (euclideanComplexInclusion (C (hermitianContinuousBilinear A V)) -
      Complex.I • euclideanComplexInclusion
        (C (hermitianContinuousBilinear A (Complex.I • V))))) i
  simp only [map_smul, smul_apply, smul_sub, smul_comm Complex.I a]

/-- On the original carrier, the common zero coefficient is exactly the
measured normal square and the square of the literal supplied cutoff. No
response operator or frequency appears in that endpoint
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_background:eq:bg-T`). -/
theorem correctedTransportCrossHomotopy_zero_on_carrier (τ : ℝ)
    {z : Euclidean 3} (hz : z ∈ closedBall z₀ ρ) (x : Euclidean (m + 1)) :
    let w := (x, (z, T.reference.spatialPatch z))
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ (0, w) =
      (κ w) ^ 2 • euclideanComplexInclusion (C x
        (fun i j ↦ ‖fullNormal T Q F row col Φ Y r w‖ ^ 2 *
          phaseGradient T Q x (T.reference.spatialPatch z) i *
          phaseGradient T Q x (T.reference.spatialPatch z) j)) := by
  intro w
  have hinsert : retainedCarrierInsertion T z₀ hρ w = w := by
    dsimp [retainedCarrierInsertion, w]
    rw [extendedRetainedCarrier_eq T z₀ hρ hz]
  rw [correctedTransportCrossHomotopy_zero, hinsert,
    complexCrossMeasurement_real_smul_left, smul_apply,
    (complexCrossMeasurement (C x) _).map_smul_of_tower, smul_smul]
  have hprincipal : fullLeadingPrincipalMatrix T Q F row col Φ Y r w =
      (principalMatrix (fullNormal T Q F row col Φ Y r w)
        (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal := rfl
  simp only [hprincipal, complexCrossMeasurement_principalMatrix, pow_two]
  rfl

/-- Apply the SAME full/carrier scalar compatibility to the corrected zero
coefficient. This identifies the actual measured squared normal required by
the original prepared native kernel, before its unchanged Fourier masks
(`app:ch_background:eq:bg-T`, `app:ch_mean_pairs:eq:mean-normal-comparison`). -/
theorem correctedTransportCrossHomotopy_zero_eq_compatible_carrier
    (φ y : ℝ × (Euclidean (m + 1 - 1) × Euclidean 3) →
      Euclidean (m + 1 - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (m + 1 - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y r (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w)
    {p : Euclidean (m + 1) × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2) ∈ V)
    (hz : parameter p.2 ∈ closedBall z₀ ρ) (τ : ℝ) :
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ
        (0, carrierGraph T p) =
      (κ (carrierGraph T p)) ^ 2 • euclideanComplexInclusion (C p.1
        (fun i j ↦ ‖normalField T Q F row col φ y r p.1 p.2‖ ^ 2 *
          T.carrierGradient Q p.1 (parameter p.2) i *
          T.carrierGradient Q p.1 (parameter p.2) j)) := by
  have hn := normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y r hcompat hp
  have h := correctedTransportCrossHomotopy_zero_on_carrier
    T Q F row col Φ Y χ B r κ C z₀ hρ τ hz p.1
  change correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ
      (0, carrierGraph T p) =
    (κ (carrierGraph T p)) ^ 2 • euclideanComplexInclusion (C p.1
      (fun i j ↦ ‖fullNormal T Q F row col Φ Y r (carrierGraph T p)‖ ^ 2 *
        phaseGradient T Q p.1 (T.reference.spatialPatch (parameter p.2)) i *
        phaseGradient T Q p.1 (T.reference.spatialPatch (parameter p.2)) j)) at h
  rw [← hn, phaseGradient_on_carrier] at h
  exact h

end JanetCartan.Sampling.CorrectedTransport
