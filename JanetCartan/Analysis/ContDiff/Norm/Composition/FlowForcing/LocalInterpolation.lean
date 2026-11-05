module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Profiles

import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Baseline-one interpolation on a buffered open domain

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:elementary-interpolation-jets` of paper.tex, a map smooth on an open
neighborhood of the working closed ball has the same interpolation profiles
as a globally smooth map. The existing cutoff extension agrees near every
point of the ball, so every ambient derivative seminorm is preserved exactly,
including at boundary points. No bounds on the extension outside the ball enter.

This supplies the local interpolation input for the buffered-domain flow-forcing
estimate. The constant is chosen before the function and its high norms, and
one constant controls both endpoint orders and every intermediate order.
-/

public section

open scoped ContDiff

namespace JanetCartan.FlowForcing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`, using the genuine
interpolation of `app:lem:elementary-interpolation-jets`: a uniform baseline-one
profile for maps smooth on an explicit open neighborhood of a positive-radius
closed ball. This is the interpolation input for buffered-domain flow forcing.
The codomain need not be finite-dimensional or complete. -/
theorem exists_uniform_cNorm_baseline_one_profile_closedBall_on (a : E) {ρ : ℝ}
    (hρ : 0 < ρ) {U : Set E} (hU : IsOpen U) (hball : Metric.closedBall a ρ ⊆ U)
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ g : E → F, ContDiffOn ℝ ∞ g U →
      cNorm (Metric.closedBall a ρ) 1 g ≤ M → ∀ j, 1 ≤ j → j ≤ n →
      cNorm (Metric.closedBall a ρ) j g ≤
        K * (1 + cNorm (Metric.closedBall a ρ) n g) ^ (((j : ℝ) - 1) / (n - 1)) := by
  obtain ⟨K, hK, hprofile⟩ :=
    exists_uniform_cNorm_baseline_one_profile_closedBall (F := F) a hρ hn hM
  refine ⟨K, hK, ?_⟩
  intro g hg hgM j hj hjn
  obtain ⟨f, hf, _, _, hfg⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall a hρ hU hball hg
  have hnorm : ∀ r, cNorm (Metric.closedBall a ρ) r f =
      cNorm (Metric.closedBall a ρ) r g :=
    GeometricProfile.cNorm_eq_of_eventuallyEq hfg
  have hfM : cNorm (Metric.closedBall a ρ) 1 f ≤ M := by
    simpa only [hnorm] using hgM
  simpa only [hnorm] using hprofile f hf hfM j hj hjn

end JanetCartan.FlowForcing
