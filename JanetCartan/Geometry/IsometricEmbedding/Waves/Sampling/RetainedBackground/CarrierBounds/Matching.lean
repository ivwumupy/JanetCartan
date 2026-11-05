module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CarrierBounds.Geometry

/-!
# Literal matching on the prescribed background measurements

The existing extension is removed only on the original `χ` and `ψ` support.
The nonzero endpoint is the actual atom differential; the zero endpoint is
exactly `backgroundPolynomial_zero`, with the SAME covector and scalar.
Consumer: `app:ch_waves:eq:background-quadrature` and its adjacent transport comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open ActualCarriers FrozenMenu CurrentFullPhase MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation AmbientResponse ResponseTransfer

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)

/-- On the original measured support, neither auxiliary extension changes
the tensor or its carrier covector (`app:ch_waves:eq:background-quadrature`). -/
theorem weighted_retainedCarrierPullback_eq
    (χ : Euclidean (m + 1) → ℝ) (ψ : SeparatedSampling.Point → ℝ)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ z, ψ z ≠ 0 → (WithLp.toLp 2 z,
      T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ closedBall a.2 (ρ / 4))
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (τ : ℝ) (z : SeparatedSampling.Point) (x : Euclidean (m + 1)) :
    ψ z • retainedCarrierPullback T a hρ χ H τ z x =
      ψ z • (χ x • H (τ, (x, (WithLp.toLp 2 z,
        T.reference.spatialPatch (WithLp.toLp 2 z))))) := by
  by_cases hz : ψ z = 0
  · simp only [hz, zero_smul]
  by_cases hx : χ x = 0
  · simp only [retainedCarrierPullback, supportedJointTensor, retainedCarrierPoint,
      hx, mul_zero, zero_smul, smul_zero]
  have hzg := hψ z hz
  have hzc : WithLp.toLp 2 z ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hzg
    exact closedBall_subset_closedBall (by linarith) hzg.1
  have hw : (x, (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z))) ∈
      closedBall a (ρ / 2) := by
    rw [← closedBall_prod_same]
    exact ⟨hχ hx, closedBall_subset_closedBall (by linarith) hzg⟩
  simp only [retainedCarrierPullback, retainedCarrierPoint,
    extendedRetainedCarrier_eq T a.2.1 hρ hzc, supportedJointTensor_eq a hρ χ H τ hw]

variable
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)

/-- The actual retained background for quadrature, pulled back from the
supported polynomial without changing any retained field
(`app:ch_waves:eq:background-quadrature`). -/
def retainedBackgroundCarrier (χ : Euclidean (m + 1) → ℝ)
    (τ : ℝ) (z : SeparatedSampling.Point) (x : Euclidean (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  retainedCarrierPullback T a hρ χ
    (fun q ↦ backgroundPolynomial T Q F row col Φ Y r q.1 q.2) τ z x

/-- Exact weighted agreement with the original background at every nonzero
inverse frequency. Coefficient regularity comes from the retained leading
outputs through `localizedBackground_eq_polynomial_of_leading_outputs`
(`app:ch_waves:eq:background-quadrature`). -/
theorem weighted_retainedBackgroundCarrier_eq_localized
    {Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hball : closedBall a (ρ / 2) ⊆ Ω)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean (m + 1) → ℝ) (ψ : SeparatedSampling.Point → ℝ)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ z, ψ z ≠ 0 → (WithLp.toLp 2 z,
      T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ closedBall a.2 (ρ / 4))
    {τ : ℝ} (hτ : τ ≠ 0) (z : SeparatedSampling.Point) (x : Euclidean (m + 1)) :
    ψ z • retainedBackgroundCarrier T a hρ Q F row col Φ Y r χ τ z x =
      ψ z • localizedBackground T Q F row col Φ Y r χ τ (WithLp.toLp 2 z) x := by
  rw [retainedBackgroundCarrier, weighted_retainedCarrierPullback_eq T a hρ χ ψ hχ hψ]
  by_cases hz : ψ z = 0
  · simp only [hz, zero_smul]
  by_cases hx : χ x = 0
  · simp only [localizedBackground, hx, zero_smul, smul_zero]
  have hw : (x, (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z))) ∈ Ω := by
    apply hball
    rw [← closedBall_prod_same]
    exact ⟨hχ hx, closedBall_subset_closedBall (by linarith) (hψ z hz)⟩
  rw [localizedBackground_eq_polynomial_of_leading_outputs T Q F row col Φ Y r
    hΩ hspace hphase hF hi hrank hα hnonzero χ hτ hw]

/-- The weighted zero endpoint remains the original transported rank-one
tensor, including its original scalar amplitude and carrier covector
(the comparison adjacent to `app:ch_waves:eq:background-quadrature`). -/
theorem weighted_retainedBackgroundCarrier_zero
    (χ : Euclidean (m + 1) → ℝ) (ψ : SeparatedSampling.Point → ℝ)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψ : ∀ z, ψ z ≠ 0 → (WithLp.toLp 2 z,
      T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ closedBall a.2 (ρ / 4))
    (z : SeparatedSampling.Point) (x : Euclidean (m + 1)) :
    ψ z • retainedBackgroundCarrier T a hρ Q F row col Φ Y r χ 0 z x =
      ψ z • (χ x • (fun i j ↦
        ‖principalNormal (canonicalNormalCompletion F x)
          (phaseGradient T Q x (T.reference.spatialPatch (WithLp.toLp 2 z)))
          (fullLeadingCovector T Q F row col Φ Y r
            (x, (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z))))‖ ^ 2 *
        phaseGradient T Q x (T.reference.spatialPatch (WithLp.toLp 2 z)) i *
        phaseGradient T Q x (T.reference.spatialPatch (WithLp.toLp 2 z)) j)) := by
  rw [retainedBackgroundCarrier, weighted_retainedCarrierPullback_eq T a hρ χ ψ hχ hψ]
  rw [backgroundPolynomial_zero]

end JanetCartan.Sampling.RetainedBackground
