module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.CorrectedSamplingData
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.MaskedPullback
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.Support

/-!
# The corrected sampling product at a fixed physical rate

The normal homotopy changes only the covector of the modulated factor.
Both corrected factors retain their supplied nonzero physical inverse frequency.
The coefficient cutoff, real measurement, carrier, detector and high-pass are
the ones in `CanonicalRowComparison.correctedColoredCrossBandData`.
The consumer is the amplitude and support matching in the uniform colored mean
estimate (`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.CorrectedMean
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude FullNormalGeometry FullNormalGeometry.PhaseJets FullPhaseCharts
open MeanNormalBound.NormalizedFullPhase ContinuumRow RawPrimary.MaskProfiles
open RawKernel RawInputPartition

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

/-- The literal two corrected factors at one fixed physical inverse frequency.
The background receives no detector or high-pass
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def fixedRateCrossCoefficient (τ : ℝ)
    (w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  complexCrossMeasurement (C w.1)
    (κ (w.1, w.2.1, extendedRetainedCarrier T z₀ hρ w.2.1) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
        (w.1, w.2.1, extendedRetainedCarrier T z₀ hρ w.2.1))
    (κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w)

/-- The corrected normal homotopy. Its physical rate `τ` is fixed while `ε`
varies only the shifted covector. The unused first slot of the existing
pullback is discarded, so no regularity in the solver's rate is asserted
(`app:ch_waves:eq:phase-quotient`, `app:ch_osc:setup:osc-normal`). -/
def fixedRateNormalAmplitude (τ : ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean (m + 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedMeasuredPullback T ψ angular highPass
    (fun q ↦ fixedRateCrossCoefficient T Q F row col Φ Y χ B r κ C z₀ hρ τ q.2)
    j (ε, v, x, u)

variable (τ : ℝ)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- Literal insertion of the normalized covector, retaining the same physical
rate in both corrected factors, including when the homotopy parameter is zero
(`app:ch_waves:eq:phase-quotient`). -/
theorem fixedRateNormalAmplitude_literal (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j v ε x (fullInputCoordinates m (s, θ)) =
      ((ψ (carrierSamplingEquiv (s, v)) : ℂ) *
        normalizedMask (n := m + 1) angular highPass j θ) •
          fixedRateCrossCoefficient T Q F row col Φ Y χ B r κ C z₀ hρ τ
            (x, carrierParameters (v, s),
              T.reference.spatialPatch (carrierParameters (v, s)) + ε • θ) := by
  simp only [fixedRateNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedPoint, normalizedRetainedMask, inputCoordinates_apply,
    adapted_canonicalInputCoordinates]

/-- A nonzero corrected homotopy retains the actual physical coefficient
support, carrier weight and complete wide band. This is valid at fixed `τ`
without any assumption at physical rate zero
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fixedRateNormalAmplitude_nonzero (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (hn : fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j v ε x (fullInputCoordinates m (s, θ)) ≠ 0) :
    x ∈ Prod.fst '' Function.support κ ∧ ψ (carrierSamplingEquiv (s, v)) ≠ 0 ∧
      1 / 2 < ‖θ‖ ∧ ‖θ‖ < 2 := by
  rw [fixedRateNormalAmplitude_literal] at hn
  have hm : normalizedMask (n := m + 1) angular highPass j θ ≠ 0 := by
    intro hz
    exact hn (by simp only [hz, mul_zero, zero_smul])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨(x, carrierParameters (v, s),
        T.reference.spatialPatch (carrierParameters (v, s)) + ε • θ), ?_, rfl⟩
    intro hz
    exact hn (by simp only [fixedRateCrossCoefficient, hz, zero_smul, map_zero, smul_zero])
  · intro hz
    exact hn (by simp only [hz, Complex.ofReal_zero, zero_mul, zero_smul])
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_le (n := m + 1) angular highPass j hh))
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_ge (n := m + 1) angular highPass j hh))

/-- The corrected homotopy vanishes off the original full-input domain.
No detector transition or sharp Hilbert refinement is discarded
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fixedRateNormalAmplitude_eq_zero_off_fullInputDomain {R Pψ : ℝ}
    (hψ : SeparatedSampling.PatchBounds ψ R Pψ)
    (j : ℕ) (v : Euclidean 2) (ε : ℝ) (u : Euclidean (m + 1))
    (hu : u ∉ fullInputDomain m 0 R) (x : Euclidean (m + 1)) :
    fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j v ε x u = 0 := by
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  by_contra hn
  obtain ⟨_, hz, hlo, hhi⟩ := fixedRateNormalAmplitude_nonzero
    T Q F row col Φ Y χ B r κ C z₀ hρ τ angular highPass ψ j v ε x s θ hn
  apply hu
  rw [fullInputCoordinates_mem_domain]
  refine ⟨?_, ?_⟩
  · have hh := hψ.support _ hz 0
    change |s| ≤ R at hh
    exact abs_le.mp hh
  · constructor
    · norm_num only [dyadicScale, pow_zero, one_div, mem_closedBall, dist_zero_right]
      exact hhi.le
    · simpa only [dyadicScale, pow_zero, one_div, mem_ball, dist_zero_right, not_lt]
        using hlo.le

/-- The supplied physical and angular supports put the literal corrected
amplitude in the same radial normal chart. This uses the complete detector
support, not merely its central direction
(`app:ch_osc:setup:osc-normal`). -/
theorem support_fixedRateNormalAmplitude_subset
    (hangular : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    {ηb : Euclidean (m + 1 - 1)} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 → NormedSpace.normalize θ ∈
      CanonicalConic.closedDirections (n := m + 1) ηb radius)
    {X₀ : Set (Euclidean (m + 1))} (hκ : Prod.fst '' Function.support κ ⊆ X₀)
    (v : Euclidean 2)
    (hψ : ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ closedBall (z₀ 0) radius)
    (j : ℕ) (ε : ℝ) :
    Function.support (Function.uncurry
      (fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
        angular highPass ψ j v ε)) ⊆
      X₀ ×ˢ radialSamplingSupport T z₀ ηb radius amin amax := by
  rintro ⟨x, u⟩ hn
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  obtain ⟨hx, hz, hθlo, hθhi⟩ := fixedRateNormalAmplitude_nonzero
    T Q F row col Φ Y χ B r κ C z₀ hρ τ angular highPass ψ j v ε x s θ hn
  have hθangle : angular θ ≠ 0 := by
    intro ha
    apply hn
    rw [Function.uncurry_apply_pair, fixedRateNormalAmplitude_literal,
      normalizedMask_eq_fixed_radial (n := m + 1) angular highPass hangular]
    simp only [ha, zero_mul, mul_zero, zero_smul]
  have hwide : θ ∈ wideBand (m + 1) 0 := by
    constructor
    · norm_num only [dyadicScale, pow_zero, one_div, mem_closedBall, dist_zero_right]
      exact hθhi.le
    · simpa only [dyadicScale, pow_zero, one_div, mem_ball, dist_zero_right, not_lt]
        using hθlo.le
  exact ⟨hκ hx, wideBand_mem_radialSamplingSupport T hηb hradius
    (hψ s hz) hlo hhi hwide (hangle θ hθangle)⟩

end JanetCartan.Sampling.CorrectedMean
