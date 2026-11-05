module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.UniformRectangles
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FactorWeights

/-!
# Four fixed weights on the uniform comparison rectangles

The centers in `UniformRectangles` are fixed before the current symbol, so
membership in its varying canonical source is not part of their type. This
adapter constructs the existing four weights at exactly those centers, before
any source is chosen (`app:ch_regular:thm:no-return`).
-/

@[expose] public noncomputable section
open Set Metric

namespace JanetCartan.ProtectedFlow.PhaseCover
open FiniteChain.Retarded

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Construct all four weights at fixed canonical centers, with simultaneous
source and target plateaus on their inner cover. Composing this conclusion
with the complete-source cover of
`exists_finite_comparison_cover_with_uniform_rectangles` retains the same
centers and weights for every admissible current symbol
(`app:ch_regular:thm:no-return`). -/
theorem exists_canonicalFactorWeights_on_fixed_centers
    (centers : Finset (CanonicalPhase V)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w : (q : centers) → CanonicalFactorWeights q.1 ρ,
      ∀ z ∈ ⋃ q ∈ centers, ball q (ρ / 8), ∃ q : centers,
        (w q).base 0 z.1 * (w q).frequency z.2 = 1 ∧
        (w q).base 1 z.1 * (w q).frequency z.2 = 1 := by
  classical
  let w (q : centers) : CanonicalFactorWeights q.1 ρ :=
    Classical.choice (exists_canonicalFactorWeights q.1 hρ)
  refine ⟨w, ?_⟩
  intro z hz
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz
  have hin : z ∈ closedBall q (ρ / 4) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ρ / 8 ≤ ρ / 4)) hzq
  exact ⟨⟨q, hq⟩, (w ⟨q, hq⟩).localized_base_eq_one 0 hin,
    (w ⟨q, hq⟩).localized_base_eq_one 1 hin⟩

end JanetCartan.ProtectedFlow.PhaseCover
