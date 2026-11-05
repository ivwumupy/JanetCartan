module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportedNormal

/-!
# Exact amplitude matching for the supported measured raw kernel

The constructed normal homotopy and smooth-band kernel use the SAME extended
raw polynomial. The identities below supply the amplitude equation of
`LiteralMeanBound.exists_source_mean_bound`, with the original square-root
Jacobian, half derivative, Fourier scalar and both complex quadratures.
No equality between independently constructed amplitudes is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open RawKernel FullNormalGeometry.PhaseJets RawPrimary.MaskProfiles
open MeanNormalBound.NormalizedFullPhase ContinuumRow

variable {m N J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- The normalized extended raw coefficient equals the supported normal
homotopy at `ε = τ 2^j`, including at zero. No inverse-frequency formula or
differentiability hypothesis is needed for this polynomial identity
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedMeasuredNormalAmplitude_eq_normalized
    (τ : ℝ) (j : ℕ) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular H ψ j v (τ * (2 : ℝ) ^ j) x (fullInputCoordinates m (s, θ)) =
      normalizedMeasuredAmplitude
        (supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ τ)
        T.reference.spatialPatch (fun _ ↦ τ) (detectorMask (n := m + 1) angular H) j
        (carrierParameters (v, s)) (ψ (carrierSamplingEquiv (s, v))) x θ := by
  have hp : ((2 : ℝ) ^ j)⁻¹ * (τ * (2 : ℝ) ^ j) = τ := by
    field_simp
  simp only [supportedMeasuredNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedMask, normalizedRetainedPoint, inputCoordinates_apply,
    adapted_canonicalInputCoordinates, hp, supportedMeasuredDerivativePolynomial,
    normalizedMeasuredAmplitude, normalizedMask, mul_assoc]

/-- Literal `hamplitude` matching for the SAME smooth-band kernel and
constructed nonzero homotopy. It retains the original Lebesgue dilation,
half derivative and Fourier normalization exactly
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedMeasuredBandAmplitude_normalization
    (τ : ℝ) (j : Fin J) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (i : Fin (m + 1)) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * (ψ (carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) *
      detectorMask (n := m + 1) angular H ((2 : ℝ) ^ j.val • θ) *
      measuredBandAmplitude
        (supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ τ)
        T.reference.spatialPatch (fun _ ↦ τ)
        (((j, carrierParameters (v, s)), (2 : ℝ) ^ j.val • θ), x) i =
      (NormalComparison.normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
          angular H ψ j.val v (τ * (2 : ℝ) ^ j.val) x (fullInputCoordinates m (s, θ)) i := by
  rw [supportedMeasuredNormalAmplitude_eq_normalized]
  exact measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
    (supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ τ)
    T.reference.spatialPatch (fun _ ↦ τ) (detectorMask (n := m + 1) angular H) j
    (carrierParameters (v, s)) (ψ (carrierSamplingEquiv (s, v))) x θ i

end JanetCartan.Sampling.MeasuredAmplitude
