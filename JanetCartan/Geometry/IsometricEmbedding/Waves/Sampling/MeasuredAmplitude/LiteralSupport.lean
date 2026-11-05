module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.Support
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles

/-!
# The measured homotopy in the original sampling coordinates

Identify the actual normalized mask, retaining its high-pass transition,
half derivative and smooth wide band. Its support fits the entire radial core
of the full phase geometry. These are the literal amplitude and support inputs
of `LiteralMeanBound.exists_source_mean_bound`, for
`app:ch_waves:eq:sampling-operator-bounds`. No sharp refinement indicator is
introduced into the smooth amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open RawKernel RawPrimary.MaskProfiles FullNormalGeometry
open MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap
open ContinuumRow ContinuumRow.CanonicalConic ContinuumNormalReduction.ConicChart

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean m × (Euclidean 3 × Euclidean m)) →
    Euclidean m × (Euclidean 3 × Euclidean m))
  (r : Euclidean m × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (angular : Euclidean m → ℂ) (H : Euclidean m → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- Exact nonzero measured homotopy in the ORIGINAL `(s,θ)` insertion, valid
also at epsilon zero. The normalized mask is the one already constructed by
`RawPrimary.MaskProfiles`; all quadratures and every correction power remain
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullMeasuredNormalAmplitude_literal (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
      (detectorMask (n := m + 1) angular H) ψ j v ε x
      (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) =
      ((ψ (carrierSamplingEquiv (s, v)) : ℂ) * normalizedMask (n := m + 1) angular H j θ) •
        fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
          (ε / (2 : ℝ) ^ j) (carrierParameters (v, s)) x
          (T.reference.spatialPatch (carrierParameters (v, s)) + ε • θ) := by
  simp only [fullMeasuredNormalAmplitude, adapted_canonicalInputCoordinates,
    normalizedMask, mul_assoc]

/-- The support of the original measured amplitude uses the fixed physical
cutoff, carrier weight, angular support and the full wide band. This closes the
support field of the subsequent full normal data once those fixed cutoffs are
chosen inside their prescribed buffers (`app:ch_waves:setup:oscillatory`). -/
theorem support_fullMeasuredNormalAmplitude_literal_subset
    (hangular : ∀ a : ℝ, 0 < a → ∀ θ, angular (a • θ) = angular θ)
    {z₀ : Euclidean 3} {ηb : Euclidean m} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 →
      NormedSpace.normalize θ ∈ closedDirections (n := m + 1) ηb radius)
    {X₀ : Set (Euclidean (m + 1))} (hχ : Function.support χ ⊆ X₀)
    (v : Euclidean 2)
    (hψ : ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ closedBall (z₀ 0) radius)
    (j : ℕ) (ε : ℝ) :
    Function.support (fun w : Euclidean (m + 1) × Euclidean (m + 1) ↦
      fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
        (detectorMask (n := m + 1) angular H) ψ j v ε w.1 (canonicalInputCoordinates T w.2)) ⊆
      X₀ ×ˢ radialSamplingSupport T z₀ ηb radius amin amax := by
  rintro ⟨x, u⟩ hnonzero
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  rw [Function.mem_support,
    fullMeasuredNormalAmplitude_literal T Q F row col Φ Y r measurement χ angular H ψ] at hnonzero
  have hmask : normalizedMask (n := m + 1) angular H j θ ≠ 0 := by
    intro hz
    apply hnonzero
    simp only [hz, mul_zero, zero_smul]
  have hweight : ψ (carrierSamplingEquiv (s, v)) ≠ 0 := by
    intro hz
    apply hnonzero
    simp only [hz, Complex.ofReal_zero, zero_mul, zero_smul]
  have hphysical : χ x ≠ 0 := by
    intro hz
    apply hnonzero
    simp only [fullMeasuredDerivativePolynomial, hz, Complex.ofReal_zero, zero_smul,
      smul_zero]
  have hθlo : (1 / 2 : ℝ) < ‖θ‖ := lt_of_not_ge (fun hh ↦
    hmask (normalizedMask_eq_zero_of_le (n := m + 1) angular H j hh))
  have hθhi : ‖θ‖ < 2 := lt_of_not_ge (fun hh ↦
    hmask (normalizedMask_eq_zero_of_ge (n := m + 1) angular H j hh))
  have hθangle : angular θ ≠ 0 := by
    intro hz
    apply hmask
    rw [normalizedMask_eq_fixed_radial (n := m + 1) angular H hangular]
    simp only [hz, zero_mul, mul_zero]
  have hwide : θ ∈ RawInputPartition.wideBand (m + 1) 0 := by
    constructor
    · norm_num [RawInputPartition.dyadicScale, mem_closedBall, dist_zero_right]
      exact hθhi.le
    · simpa only [RawInputPartition.dyadicScale, pow_zero, one_div, mem_ball,
        dist_zero_right, not_lt] using hθlo.le
  exact ⟨hχ hphysical, wideBand_mem_radialSamplingSupport T hηb hradius
    (hψ s hweight) hlo hhi hwide (hangle θ hθangle)⟩

/-- The transported zero endpoint is the SAME leading principal matrix,
with the original detector, carrier weight and both quadratures. It is not the
zero reference amplitude used to construct the phase geometry
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem fullMeasuredNormalAmplitude_literal_zero (j : ℕ) (v : Euclidean 2)
    (x : Euclidean (m + 1)) (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    fullMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ
      (detectorMask (n := m + 1) angular H) ψ j v 0 x
      (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) =
      ((ψ (carrierSamplingEquiv (s, v)) : ℂ) * normalizedMask (n := m + 1) angular H j θ) •
        ((χ x : ℂ) • measurement x
          (RawPrimary.fullLeadingPrincipalMatrix T Q F row col Φ Y r
            (x, (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s)))))) := by
  rw [fullMeasuredNormalAmplitude_literal]
  simp only [zero_div, zero_smul, add_zero, fullMeasuredDerivativePolynomial_zero]

end JanetCartan.Sampling.MeasuredAmplitude
