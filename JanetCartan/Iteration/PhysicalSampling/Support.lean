module

public import JanetCartan.Iteration.PhysicalSampling.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.LiteralSupport

/-!
# Literal normalization and support of the scalar auxiliary row

The scalar kernel uses the same half derivative, Fourier scalar and smooth
radial partition as the measured kernel. Its support follows from the original
physical cutoff, carrier weight and angular detector, not from an assumed
normal-operator estimate. Consumer: the full scalar normal geometry for
`new:eq:amplitude-test` and `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open Sampling Sampling.RawKernel Sampling.MeasuredAmplitude
open Sampling.FullNormalGeometry Sampling.FullNormalGeometry.PhaseJets
open Sampling.MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles PhysicalMean ContinuumRow ContinuumRow.CanonicalConic

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The scalar amplitude in the original incidence/transverse variables;
the chosen epsilon, carrier center and stress frame do not enter it. -/
theorem scalarNormalizedAmplitude_literal
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (ε : ℝ) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    scalarNormalizedAmplitude T χ ψ angular H j (ε, v, x, fullInputCoordinates m (s, θ)) =
      ((ψ (carrierSamplingEquiv (s, v)) : ℂ) * normalizedMask angular H j θ) •
        scalarAuxiliaryAmplitude (by omega) χ () x 0 := by
  simp only [scalarNormalizedAmplitude, normalizedRetainedMask, inputCoordinates_apply,
    adapted_canonicalInputCoordinates]

/-- Exact scalar-kernel normalization for arbitrary retained parameter labels.
It preserves the square-root Jacobian and the actual original radial band. -/
theorem scalarAuxiliaryBandAmplitude_normalization
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    {Z : Type*} (ζ : Z → Euclidean (m + 1 - 1)) (τ : Z → ℝ)
    {J : ℕ} (j : Fin J) (p : Z) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (i : Fin (m + 1)) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * (ψ (carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) *
      detectorMask angular H ((2 : ℝ) ^ j.val • θ) *
      measuredBandAmplitude (scalarAuxiliaryAmplitude (by omega) χ) ζ τ
        (((j, p), (2 : ℝ) ^ j.val • θ), x) i =
      (NormalComparison.normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        scalarNormalizedAmplitude T χ ψ angular H j.val
          (τ p * (2 : ℝ) ^ j.val, v, x, fullInputCoordinates m (s, θ)) i := by
  rw [scalarNormalizedAmplitude_literal]
  have hh := measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
    (scalarAuxiliaryAmplitude (by omega) χ) ζ τ (detectorMask angular H) j p
    (ψ (carrierSamplingEquiv (s, v))) x θ i
  simpa only [normalizedMeasuredAmplitude, normalizedMask, scalarAuxiliaryAmplitude,
    Nat.add_sub_cancel, mul_assoc] using hh

/-- The actual support fits the same prescribed radial full-input geometry.
All premises are geometric supports of the original masks, not analytic norm
bounds or independently chosen successful samples. -/
theorem support_scalarNormalizedAmplitude_subset
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (hangular : ∀ a : ℝ, 0 < a → ∀ θ, angular (a • θ) = angular θ)
    {z₀ : Euclidean 3} {ηb : Euclidean m} (hηb : ηb ≠ 0)
    {radius amin amax : ℝ} (hradius : 0 < radius)
    (hlo : amin ≤ (1 / 2) / ‖ηb‖) (hhi : 2 / ‖ηb‖ ≤ amax)
    (hangle : ∀ θ, angular θ ≠ 0 →
      NormedSpace.normalize θ ∈ closedDirections (n := m + 1) ηb radius)
    {X₀ : Set (Euclidean (m + 1))} (hχ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ X₀)
    (v : Euclidean 2)
    (hψ : ∀ s, ψ (carrierSamplingEquiv (s, v)) ≠ 0 → s ∈ closedBall (z₀ 0) radius)
    (j : ℕ) (ε : ℝ) :
    Function.support (fun w : Euclidean (m + 1) × Euclidean (m + 1) ↦
      scalarNormalizedAmplitude T χ ψ angular H j (ε, v, w)) ⊆
        X₀ ×ˢ radialSamplingSupport T z₀ ηb radius amin amax := by
  rintro ⟨x, u⟩ hnonzero
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  rw [Function.mem_support, scalarNormalizedAmplitude_literal] at hnonzero
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
    simp only [scalarAuxiliaryAmplitude, hz, Complex.ofReal_zero, zero_smul, smul_zero]
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

/-- Every nonzero scalar coefficient lies on the original physical/carrier
supports and in the unchanged normalized radial band. -/
theorem scalarNormalizedAmplitude_nonzero
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (ε : ℝ) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (hn : scalarNormalizedAmplitude T χ ψ angular H j
      (ε, v, x, fullInputCoordinates m (s, θ)) ≠ 0) :
    χ x ≠ 0 ∧ ψ (carrierSamplingEquiv (s, v)) ≠ 0 ∧
      1 / 2 < ‖θ‖ ∧ ‖θ‖ < 2 := by
  rw [scalarNormalizedAmplitude_literal] at hn
  have hm : normalizedMask (n := m + 1) angular H j θ ≠ 0 := by
    intro hz
    exact hn (by simp only [hz, mul_zero, zero_smul])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    exact hn (by simp only [scalarAuxiliaryAmplitude, hz, Complex.ofReal_zero,
      zero_smul, smul_zero])
  · intro hz
    exact hn (by simp only [hz, Complex.ofReal_zero, zero_mul, zero_smul])
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_le (n := m + 1) angular H j hh))
  · exact lt_of_not_ge (fun hh ↦ hm
      (normalizedMask_eq_zero_of_ge (n := m + 1) angular H j hh))

/-- The literal full-input restriction follows from the existing carrier and
radial masks; it is not an additional operator-support hypothesis. -/
theorem scalarNormalizedAmplitude_eq_zero_off_fullInputDomain
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
    (hψ : SeparatedSampling.PatchBounds ψ R Pψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (v : Euclidean 2) (ε : ℝ) (u : Euclidean (m + 1))
    (hu : u ∉ fullInputDomain m 0 R) (x : Euclidean (m + 1)) :
    scalarNormalizedAmplitude T χ ψ angular H j (ε, v, x, u) = 0 := by
  obtain ⟨⟨s, θ⟩, rfl⟩ := (fullInputCoordinates m).surjective u
  by_contra hn
  obtain ⟨_, hψ₀, hlo, hhi⟩ := scalarNormalizedAmplitude_nonzero
    T χ ψ angular H j ε v x s θ hn
  apply hu
  rw [fullInputCoordinates_mem_domain]
  refine ⟨?_, ?_⟩
  · have hh := hψ.support _ hψ₀ 0
    change |s| ≤ R at hh
    exact abs_le.mp hh
  · constructor
    · norm_num only [RawInputPartition.dyadicScale, pow_zero, one_div,
        mem_closedBall, dist_zero_right]
      exact hhi.le
    · simpa only [RawInputPartition.dyadicScale, pow_zero, one_div, mem_ball,
        dist_zero_right, not_lt] using hlo.le

end JanetCartan.PhysicalSampling
