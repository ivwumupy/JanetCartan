module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.MaskedPullback

/-!
# The supported actual sampling amplitude

Insert the SAME measured WKB polynomial, with its fixed raw extension, into
the original full-input coordinates. The carrier refinement and the original
measurement support put every nonzero kernel value on the extension plateau.
Thus no measured field, normal or zero endpoint is changed. The resulting
amplitude is the one used for `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open RawKernel FullNormalGeometry FullNormalGeometry.PhaseJets
open MeanNormalBound.NormalizedFullPhase ContinuumRow ContinuumRow.CanonicalConic
open RawPrimary.MaskProfiles MeanNormalBound.CanonicalGap

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
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

/-- The actual globally extended measured coefficient before the carrier
weight and dyadic masks. This is the common amplitude supplied to
`RawKernel.bandKernelData` (`app:ch_waves:eq:sampling-prefix-normal`). -/
def supportedMeasuredDerivativePolynomial (τ : ℝ) (z : Euclidean 3)
    (x : Euclidean (m + 1)) (ξ : Euclidean (m + 1 - 1)) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  retainedAmplitudeCutoff a hρ (x, (z, ξ)) •
    fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ τ z x ξ

/-- Actual nonzero normal amplitude in the ORIGINAL input coordinates. Its
extension multiplies the original raw polynomial by the already fixed cutoff;
agreement with the measured raw family is proved below
(`app:ch_waves:setup:oscillatory`). -/
def supportedMeasuredNormalAmplitude (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean (m + 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedMeasuredPullback T ψ angular H
    (fun q ↦ retainedAmplitudeCutoff a hρ q.2 •
      fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
        q.1 q.2.2.1 q.2.1 q.2.2.2) j (ε, v, x, u)

/-- The extension equals the SAME raw measured homotopy everywhere, not just
almost everywhere or on a smaller input set. The geometric carrier condition
is supplied by `RetainedGrades.exists_finite_retained_graded_raw_family`'s
buffered refinement; the physical support is the selected measurement.
Both quadratures, the full high-pass transition and epsilon zero are retained
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedMeasuredNormalAmplitude_eq
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (j : ℕ) (v : Euclidean 2) {ε : ℝ} (hε : |ε| ≤ ρ / 8)
    (x u : Euclidean (m + 1)) :
    supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular H ψ j v ε x u =
      fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
        (detectorMask (n := m + 1) angular H) ψ j v ε x (canonicalInputCoordinates T u) := by
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  rw [fullMeasuredNormalAmplitude_literal]
  simp only [supportedMeasuredNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedPoint, normalizedRetainedMask, inputCoordinates_apply,
    adapted_canonicalInputCoordinates]
  by_cases hψ₀ : ψ (carrierSamplingEquiv (s, v)) = 0
  · simp only [hψ₀, Complex.ofReal_zero, zero_mul, zero_smul]
  by_cases hm : normalizedMask (n := m + 1) angular H j θ = 0
  · simp only [hm, mul_zero, zero_smul]
  by_cases hχ₀ : χ x = 0
  · simp only [fullMeasuredDerivativePolynomial, hχ₀, Complex.ofReal_zero,
      zero_smul, smul_zero]
  have hθ : ‖θ‖ ≤ 2 := (lt_of_not_ge (fun hh ↦
    hm (normalizedMask_eq_zero_of_ge (n := m + 1) angular H j hh))).le
  rw [retainedAmplitudeCutoff_one a hρ
    (normalizedRetainedPoint_mem_plateau T (hχ hχ₀) (hψ s v hψ₀) hθ hε), one_smul]
  congr 2
  rw [div_eq_mul_inv, mul_comm]

/-- The support field needed by the actual full normal geometry follows
from the original masks and the proved plateau identity. There is no assumed
successful normal data (`app:ch_waves:setup:oscillatory`). -/
theorem support_supportedMeasuredNormalAmplitude_subset
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hangular : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    {z₀ : Euclidean 3} {ηb : Euclidean (m + 1 - 1)} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 →
      NormedSpace.normalize θ ∈ closedDirections
        (n := m + 1) ηb radius)
    {X₀ : Set (Euclidean (m + 1))} (hχX : Function.support χ ⊆ X₀)
    (v : Euclidean 2)
    (hψs : ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ closedBall (z₀ 0) radius)
    (j : ℕ) {ε : ℝ} (hε : |ε| ≤ ρ / 8) :
    Function.support (Function.uncurry
      (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular H ψ j v ε)) ⊆
      X₀ ×ˢ radialSamplingSupport T z₀ ηb radius amin amax := by
  have heq : Function.uncurry
      (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular H ψ j v ε) =
      fun w : Euclidean (m + 1) × Euclidean (m + 1) ↦
        fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
          (detectorMask (n := m + 1) angular H) ψ j v ε w.1
          (canonicalInputCoordinates T w.2) := by
    funext w
    exact supportedMeasuredNormalAmplitude_eq T Q F row col Φ Y r measurement χ a hρ
      angular H ψ hχ hψ j v hε w.1 w.2
  rw [heq]
  exact support_fullMeasuredNormalAmplitude_literal_subset T Q F row col Φ Y r measurement χ
    angular H ψ hangular hηb hradius hlo hhi hangle hχX v hψs j ε

end JanetCartan.Sampling.MeasuredAmplitude
