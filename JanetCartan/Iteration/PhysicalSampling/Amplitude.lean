module

public import JanetCartan.Iteration.PhysicalMean.ScalarRow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.InputJets

/-!
# The fixed scalar amplitude on the original normalized bands

The auxiliary row in `new:eq:amplitude-test` has amplitude `χ_* e₀`, independently
of the stress measurement and of the prepared source. Its normalized amplitude
below retains the original carrier weight, angular detector, high-pass transition,
radial square partition and half derivative. The three-profile identity supplies
all finite jets before any current immersion, frequency or sample is chosen.

These are the amplitude inputs for the scalar normal-data construction; the
actual phase data and their same-realization use are separate constructions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open Sampling Sampling.RawKernel Sampling.MeasuredAmplitude
open Sampling.FullNormalGeometry Sampling.FullNormalGeometry.PhaseJets
open RawPrimary.MaskProfiles PhysicalMean ContinuumRow

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The literal normalized scalar amplitude, in the same full-input coordinates
as the canonical sampling phase (`new:eq:amplitude-test`). -/
def scalarNormalizedAmplitude (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedRetainedMask T ψ angular highPass j q •
    scalarAuxiliaryAmplitude (by omega) χ () q.2.2.1 0

/-- The scalar cutoff and the original smooth-band mask are jointly smooth.
No regularity of the subsequently sampled amplitude is used here. -/
theorem contDiff_scalarNormalizedAmplitude
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hH : ContDiff ℝ ∞ highPass) (j : ℕ) :
    ContDiff ℝ ∞ (scalarNormalizedAmplitude T χ ψ angular highPass j) := by
  unfold scalarNormalizedAmplitude scalarAuxiliaryAmplitude
  exact (contDiff_normalizedRetainedMask T ψ hψ angular highPass ha hH j).smul
    ((Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp (by fun_prop))).smul contDiff_const)

/-- Normalization introduces no epsilon dependence into the scalar amplitude;
all epsilon dependence remains in the SAME phase (`new:eq:amplitude-test`). -/
theorem scalarNormalizedAmplitude_epsilon
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (ε : ℝ) (q : Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) :
    scalarNormalizedAmplitude T χ ψ angular highPass j (ε, q) =
      scalarNormalizedAmplitude T χ ψ angular highPass j (0, q) := rfl

/-- There are exactly the original three normalized high-pass profiles, not a
new cutoff and not a cardinality-dependent sum over dyadic bands. -/
theorem scalarNormalizedAmplitude_eq_min
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1) (j : ℕ) :
    scalarNormalizedAmplitude T χ ψ angular highPass j =
      scalarNormalizedAmplitude T χ ψ angular highPass (min j 2) := by
  funext q
  simp only [scalarNormalizedAmplitude, normalizedRetainedMask,
    normalizedMask_eq_min angular highPass hah hH₁ j]

/-- Actual all-order amplitude budgets, fixed before the current history,
frequency, band ceiling, phase data, and sample realization. These are finite
seminorms of the three fixed cutoff profiles, not assumed oscillatory bounds. -/
theorem exists_scalarNormalizedAmplitude_budgets
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ highPass) (hH₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    {S : Set (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))))}
    (hS : IsCompact S) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ j, ∀ q ∈ S, ∀ k,
      ‖iteratedFDeriv ℝ k (scalarNormalizedAmplitude T χ ψ angular highPass j) q‖ ≤ B k := by
  let A (j k : ℕ) := cNorm S k (scalarNormalizedAmplitude T χ ψ angular highPass j)
  let B (k : ℕ) := 1 + A 0 k + A 1 k + A 2 k
  have hA (j k : ℕ) : 0 ≤ A j k := cNorm_nonneg _ _ _
  have hB (k : ℕ) : 0 < B k := by dsimp [B]; linarith [hA 0 k, hA 1 k, hA 2 k]
  refine ⟨B, hB, ?_⟩
  intro j q hq k
  rw [scalarNormalizedAmplitude_eq_min T χ ψ angular highPass hah hH₁ j]
  have hb := norm_iteratedFDeriv_le_cNorm hS
    ((contDiff_scalarNormalizedAmplitude T χ ψ hψ angular highPass ha hH (min j 2)).of_le
      (by simp : (k : ℕ∞ω) ≤ ∞)) hq le_rfl
  apply hb.trans
  have hj : min j 2 ≤ 2 := min_le_right _ _
  interval_cases h : min j 2 <;> change A _ k ≤ B k <;>
    dsimp [B] <;> linarith [hA 0 k, hA 1 k, hA 2 k]

/-- Physical support of the actual scalar amplitude is exactly controlled by
its chosen cutoff; no coefficient or measured-stress inverse is involved. -/
theorem scalarNormalizedAmplitude_eq_zero_of_notMem_tsupport
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))))
    (hx : q.2.2.1 ∉ tsupport (χ : Euclidean (m + 1) → ℝ)) :
    scalarNormalizedAmplitude T χ ψ angular highPass j q = 0 := by
  have hz : χ q.2.2.1 = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [scalarNormalizedAmplitude, scalarAuxiliaryAmplitude, hz,
    Complex.ofReal_zero, zero_smul, smul_zero]

end JanetCartan.PhysicalSampling
