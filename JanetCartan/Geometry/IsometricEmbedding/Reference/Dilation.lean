module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Dilation.Estimates

/-!
# Uniform estimates for the dilated target

The target-dilation estimate of Proposition `main:prop:seed` in `paper.tex`.
The reference is fixed before the dilation parameter is chosen.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan

/-- Proposition `main:prop:seed`, estimate `main:eq:seed-small`: for an actual
smooth metric normalized by `g 0 = 1`, the dilated defect from a fixed flat
reference is bounded by `C * s` at every order, uniformly for `s ∈ [0, 1]`.
This is the constructive estimate consumed by
`scaledMetric_sub_inducedMetric_bound` in `Reference.lean`. -/
theorem scaledMetric_sub_inducedMetric_bound_of_contDiff {n : ℕ} (G : FlatReference n)
    {g : MetricField n} (hg : ContDiff ℝ ∞ g) (hg₀ : g 0 = 1) :
    ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      cNorm (G.domain.closureChart n) r (scaledMetric g s - inducedMetric G.map) ≤ C * s := by
  intro r
  have hflat : inducedMetric G.map = fun _ ↦ 1 := funext G.inducedMetric_eq_one
  simpa only [LocalDomain.closureChart, scaledMetric, hflat, hg₀, Pi.sub_def] using
    exists_cNorm_dilation_sub_const_bound
      (isCompact_closedBall (0 : Euclidean n) G.domain.chartRadius) hg r

end JanetCartan
