module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.DyadicSum.Kernels

/-!
# Frequency-uniform dyadic normal sums

The unmasked normal-sum estimate in the proof immediately following
`app:ch_waves:eq:sampling-operator-bounds`. Its constant is chosen before the
band count, input families, and admissible parameters. The additional input is
the primitive averaged-gradient gap on the original compact amplitude support.

This supplies the analytic dyadic-sum obligation of the sampling mean bound.
Producing the gap for the canonical phase and identifying the sampling kernels
with these actual oscillatory operators remain obligations of that construction.
-/

@[expose] public noncomputable section
open Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound
open NormalComparison AmplitudeBound RawInputPartition

/-- The full dyadic sum of actual Hilbert-adjoint normals is bounded uniformly
in the number of bands, with no logarithmic or band-count loss. The fixed
primitive-input budget and supported averaged-gradient gap produce all
amplitude estimates, and the same `2 * (n + 1)` physical derivative reserve
controls the sum (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_dyadicOscillatoryNormalOperator_bound
    {n r : ℕ} (G : UniformNormalGeometry n r) (C : ℕ → ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ B > 0, ∀ (J : ℕ) (F : Fin J → UniformNormalData G C) (ε : Fin J → ℝ),
      (∀ j, ε j ∈ Icc 0 G.ε₀) →
      (∀ j, ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
        γ ≤ ‖averagedGradient ((F j).phase (ε j)) x y u‖) →
      ‖∑ j, ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).comp
        ((F j).uniformOscillatoryOperator (dyadicScale j.val) (ε j)).adjoint‖ ≤ B := by
  classical
  obtain ⟨R, _, A, hA, hb⟩ := exists_dyadicNormalAmplitude_bounds G C hγ
  let B := (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A)
  have hB : 0 ≤ B := by
    have := fixedBoxAmplitudeConstant_nonneg n R
    dsimp [B]
    positivity
  refine ⟨B + 1, by linarith, ?_⟩
  intro J F ε hε hgap
  obtain ⟨ρ, _, hρ⟩ := exists_dyadic_frequency_support_radius G C J
  apply le_trans (norm_compactFrequencyMatrixAmplitudeOperator_le G.dimension_pos R
    (dyadicNormalAmplitude F ε) (contDiff_dyadicNormalAmplitude F ε hε) A
    (hb J F ε hε hgap) (isCompact_closedBall (0 : Euclidean n) ρ)
    (fun ξ hξ z ↦ by
      unfold dyadicNormalAmplitude
      exact Finset.sum_eq_zero (fun j _ ↦ hρ F ε hε j ξ hξ z))
    _ (sum_dyadicOscillatoryNormalOperator_ae_kernel F ε hε))
    (by dsimp [B]; linarith)

end JanetCartan.Sampling.MeanNormalBound
