module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Jets

/-!
# Joining smooth functions with matching jets

The closed-cover gluing step in the boundary-jet argument after
`app:ch_regular_base:eq:extension-collar-l2`. The analytic task of proving the
exterior series' regularity and matching its jets is separate from this lemma.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology ContDiff

namespace JanetCartan.BallExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A common Taylor field on two closed sets is a Taylor field on their union.
This is the closed-cover step of the joining argument following
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem hasFTaylorSeriesUpToOn_union {s t : Set E} (hs : IsClosed s) (ht : IsClosed t)
    {f : E → F} {P : E → FormalMultilinearSeries ℝ E F}
    (hPs : HasFTaylorSeriesUpToOn ∞ f P s) (hPt : HasFTaylorSeriesUpToOn ∞ f P t) :
    HasFTaylorSeriesUpToOn ∞ f P (s ∪ t) := by
  refine ⟨fun x hx ↦ hx.elim (hPs.zero_eq x) (hPt.zero_eq x), ?_, ?_⟩
  · intro m hm x _
    apply HasFDerivWithinAt.union
    · by_cases hx : x ∈ s
      · exact hPs.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hs.closure_eq])
    · by_cases hx : x ∈ t
      · exact hPt.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [ht.closure_eq])
  · intro m hm
    exact (hPs.cont m hm).union_of_isClosed (hPt.cont m hm) hs ht

/-- Smooth functions on two closed sets join smoothly if their one-sided
iterated derivatives agree on the intersection. This proves the gluing
implication used after `app:ch_regular_base:eq:extension-collar-l2`; it does
not assert that the Seeley formula satisfies the matching hypotheses. -/
theorem contDiffOn_union_of_matching_jets {s t : Set E} (hs : IsClosed s) (ht : IsClosed t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t) {f : E → F}
    (hfs : ContDiffOn ℝ ∞ f s) (hft : ContDiffOn ℝ ∞ f t)
    (hjets : ∀ m : ℕ, ∀ x ∈ s ∩ t,
      iteratedFDerivWithin ℝ m f s x = iteratedFDerivWithin ℝ m f t x) :
    ContDiffOn ℝ ∞ f (s ∪ t) := by
  classical
  let P := ftaylorSeriesWithin ℝ f s
  let Q := ftaylorSeriesWithin ℝ f t
  let J := s.piecewise P Q
  have hPs : HasFTaylorSeriesUpToOn ∞ f J s := by
    apply (hfs.ftaylorSeriesWithin hus).congr_series
    intro m _ x hx
    simp [J, P, hx]
  have hPt : HasFTaylorSeriesUpToOn ∞ f J t := by
    apply (hft.ftaylorSeriesWithin hut).congr_series
    intro m _ x hx
    by_cases hxs : x ∈ s
    · simpa [J, P, Q, hxs, ftaylorSeriesWithin] using (hjets m x ⟨hxs, hx⟩).symm
    · simp [J, Q, hxs]
  exact (hasFTaylorSeriesUpToOn_union hs ht hPs hPt).contDiffOn

end JanetCartan.BallExtension
