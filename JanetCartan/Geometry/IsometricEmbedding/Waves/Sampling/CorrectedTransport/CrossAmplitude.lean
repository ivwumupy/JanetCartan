module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.CrossProfiles

/-!
# The literal measured path from corrected to transport coefficients

Both slots use the same algebraic path at the original fixed response rate.
The background is evaluated at the original extended carrier and remains
unmasked. The detector, high-pass and carrier weight are inserted only by the
existing normalized pullback. At the physical endpoint the coefficient is
exactly the corrected kernel's coefficient; at zero it is independent of color.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition

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

/-- The two corrected factors interpolate to their SAME leading factors.
The background carrier has no Fourier mask
(`app:ch_mean_pairs:defn:mean-canonical`, `app:ch_waves:eq:colored-normal-comparison`). -/
def correctedTransportCrossHomotopy (τ : ℝ)
    (q : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  complexCrossMeasurement (C q.2.1)
    (correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ
      (q.1, retainedCarrierInsertion T z₀ hρ q.2))
    (correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ q)

/-- The common zero coefficient is the measured cross product of the literal
leading factors, with the original cutoffs
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportCrossHomotopy_zero (τ : ℝ) (w) :
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ (0, w) =
      complexCrossMeasurement (C w.1)
        (κ (retainedCarrierInsertion T z₀ hρ w) •
          fullLeadingPrincipalMatrix T Q F row col Φ Y r (retainedCarrierInsertion T z₀ hρ w))
        (κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w) := by
  simp only [correctedTransportCrossHomotopy, correctedTransportDerivativeHomotopy_zero]

/-- All fixed response rates have the identical zero coefficient. This is
an equality of the literal formulas, not of independently selected witnesses
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportCrossHomotopy_zero_independent (τ τ' : ℝ) (w) :
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ (0, w) =
      correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ' (0, w) := by
  rw [correctedTransportCrossHomotopy_zero, correctedTransportCrossHomotopy_zero]

/-- At the original inverse frequency both factors recover the coefficient
of `correctedColoredCrossBandData` exactly
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedTransportCrossHomotopy_self {τ : ℝ} (hτ : τ ≠ 0) (w) :
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ (τ, w) =
      fixedRateCrossCoefficient T Q F row col Φ Y χ B r κ C z₀ hρ τ w := by
  simp only [correctedTransportCrossHomotopy, correctedTransportDerivativeHomotopy_self
    T Q F row col Φ Y χ B r κ hτ, fixedRateCrossCoefficient, retainedCarrierInsertion]

/-- The supplied physical/carrier cutoff continues to support every point
of the transport path (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem correctedTransportCrossHomotopy_eq_zero (τ t : ℝ) (w) (hw : κ w = 0) :
    correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ (t, w) = 0 := by
  simp only [correctedTransportCrossHomotopy, correctedTransportDerivativeHomotopy,
    correctedTransportScaledError, hw, zero_smul, smul_zero, add_zero, map_zero]

/-- The original normalized measured pullback on the corrected transport
path. The physical response is fixed at `τ`, while the interpolation parameter
is `ε / 2^j` (`app:ch_waves:eq:phase-quotient`). -/
def correctedTransportNormalAmplitude (τ : ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean (m + 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedMeasuredPullback T ψ angular highPass
    (correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ)
    j (ε, v, x, u)

variable (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- The physical normalized endpoint equals the corrected mean amplitude
with both original factors and every mask unchanged
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportNormalAmplitude_self {τ : ℝ} (hτ : τ ≠ 0)
    (j : ℕ) (v : Euclidean 2) (x u : Euclidean (m + 1)) :
    correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j v (τ * (2 : ℝ) ^ j) x u =
      fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
        angular highPass ψ j v (τ * (2 : ℝ) ^ j) x u := by
  unfold correctedTransportNormalAmplitude fixedRateNormalAmplitude normalizedMeasuredPullback
  congr 1
  simp only [normalizedRetainedPoint]
  have ht : ((2 : ℝ) ^ j)⁻¹ * (τ * (2 : ℝ) ^ j) = τ := by
    field_simp
  rw [ht, correctedTransportCrossHomotopy_self T Q F row col Φ Y χ B r κ C z₀ hρ hτ]

/-- The complete normalized zero amplitude is independent of response rate,
including the high-pass transition between one and two
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportNormalAmplitude_zero_independent (τ τ' : ℝ)
    (j : ℕ) (v : Euclidean 2) (x u : Euclidean (m + 1)) :
    correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j v 0 x u =
      correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ'
        angular highPass ψ j v 0 x u := by
  simp only [correctedTransportNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedPoint, mul_zero, correctedTransportCrossHomotopy_zero]

end JanetCartan.Sampling.CorrectedTransport
