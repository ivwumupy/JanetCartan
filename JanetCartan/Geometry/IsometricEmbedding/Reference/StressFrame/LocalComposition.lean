module

public import JanetCartan.Analysis.ContDiff.Norm.Composition
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# Tame composition on an open chart domain

For `app:lem:elementary-interpolation-jets` and `app:ch_seed:eq:seed-frame-tame`,
the compact-range tame composition estimate applies to inner maps smooth only
on an open neighborhood of the closed ball. A proved smooth extension agrees
near every point of the ball, so its derivative seminorms are unchanged.
The constant is chosen before the open domain and the inner map.

The imported `JanetCartan.GeometricProfile.cNorm_eq_of_eventuallyEq` also exposes
the neighborhood-equality transfer for downstream geometric formulas.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology

namespace JanetCartan.ProjectedStressFrame

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:elementary-interpolation-jets`, used for
`app:ch_seed:eq:seed-frame-tame`: composition with a fixed coefficient smooth
near a compact range has a uniform one-high bound on a positive-radius closed
ball. The inner map need only be smooth on an open neighborhood of that ball.
The constant is independent of this neighborhood, the inner map, and its high
norms. All `r ≤ k` are allowed, including `r = k = 0`. -/
theorem exists_cNorm_comp_le_tame_closedBall_contDiffOn [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {t : Set F} (ht : IsCompact t)
    {r k : ℕ} (hrk : r ≤ k) {g : F → G}
    (hg : ∀ y ∈ t, ContDiffAt ℝ r g y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Set E), IsOpen s → Metric.closedBall x ρ ⊆ s →
      ∀ f : E → F, ContDiffOn ℝ ∞ f s →
        Set.MapsTo f (Metric.closedBall x ρ) t →
          cNorm (Metric.closedBall x ρ) r (g ∘ f) ≤
            C * (1 + cNorm (Metric.closedBall x ρ) k f) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_cNorm_comp_le_tame_closedBall_of_compact_range x hρ ht hrk hg
  refine ⟨C, hC, ?_⟩
  intro s hs hKs f hf hft
  obtain ⟨u, hu, _, _, huf⟩ :=
    exists_contDiff_extension_eq_near_closedBall x hρ hs hKs hf
  have hut : Set.MapsTo u (Metric.closedBall x ρ) t := by
    intro y hy
    rw [(huf y hy).eq_of_nhds]
    exact hft hy
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq huf k
  have hcomp : cNorm (Metric.closedBall x ρ) r (g ∘ u) =
      cNorm (Metric.closedBall x ρ) r (g ∘ f) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ r
    intro y hy
    filter_upwards [huf y hy] with z hz
    exact congrArg g hz
  simpa only [hnorm, hcomp] using hbound u hu hut

end JanetCartan.ProjectedStressFrame
