module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FactorRectangles
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.BufferedKernel

/-!
# Four weights on a complete retained canonical rectangle

For `app:ch_regular:thm:no-return`, construct the source, target and both
integral weights, with their actual closed supports in the inner rectangle.
The source and target supports lie in the plateaus of both integral weights.
The literal lower and upper operators have positive endpoint buffers. Their
complete canonical images stay in the same support rectangle; the entire
intermediate Hamilton segment therefore has the retained physical buffer.

The rectangle is supplied by `ComparisonChart.exists_factor_rectangles`.
Uniform selection of rectangles over current frames is still a producer
obligation; the weight construction itself works on any prescribed rectangle.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover FiniteChain.Retarded

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Output of the four-weight construction in `app:ch_regular:thm:no-return`.
Indices zero and one are the source and target; two and three are the input
and output integral weights. This structure is constructed below, rather than
assumed as an analytic input to the no-return construction. -/
structure CanonicalFactorWeights (c : CanonicalPhase V) (ρ : ℝ) where
  base : Fin 4 → (ℝ × V) → ℝ
  frequency : (ℝ × V) → ℝ
  base_smooth : ∀ i, ContDiff ℝ ∞ (base i)
  frequency_smooth : ContDiff ℝ ∞ frequency
  base_range : ∀ i x, base i x ∈ Icc (0 : ℝ) 1
  frequency_range : ∀ η, frequency η ∈ Icc (0 : ℝ) 1
  base_compact : ∀ i, HasCompactSupport (base i)
  frequency_compact : HasCompactSupport frequency
  base_support : ∀ i, tsupport (base i) ⊆ ball c.1 ρ
  frequency_support : tsupport frequency ⊆ ball c.2 (ρ / 2)
  inner_support : ∀ i, i.val < 2 → tsupport (base i) ⊆ ball c.1 (ρ / 2)
  base_plateau : ∀ i, closedBall c.1 (ρ / 4) ⊆ interior {x | base i x = 1}
  integral_plateau : ∀ i, 2 ≤ i.val →
    closedBall c.1 (ρ / 2) ⊆ interior {x | base i x = 1}
  frequency_plateau : closedBall c.2 (ρ / 4) ⊆ interior {η | frequency η = 1}

/-- Construct all four actual smooth weights and the frequency mask on a
prescribed rectangle. Their choices precede frequencies, derivative orders
and requested accuracy (`app:ch_regular:thm:no-return`). -/
theorem exists_canonicalFactorWeights [FiniteDimensional ℝ V]
    (c : CanonicalPhase V) {ρ : ℝ} (hρ : 0 < ρ) :
    Nonempty (CanonicalFactorWeights c ρ) := by
  obtain ⟨θ, ν, hθ, hν, hrθ, hrν, hcθ, hcν, hsθ, hsν, hpθ, hpν, _, _⟩ :=
    exists_factor_rectangle_masks c hρ
  obtain ⟨χ, hχ, hrχ, hcχ, hsχ, hpχ⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_closedBall c.1 (ρ / 2)) isOpen_ball
    (closedBall_subset_ball (by linarith : ρ / 2 < ρ))
  refine ⟨{
    base := fun i ↦ if i.val < 2 then θ else χ
    frequency := ν
    base_smooth := ?_
    frequency_smooth := hν
    base_range := ?_
    frequency_range := hrν
    base_compact := ?_
    frequency_compact := hcν
    base_support := ?_
    frequency_support := hsν
    inner_support := ?_
    base_plateau := ?_
    integral_plateau := ?_
    frequency_plateau := hpν }⟩
  · intro i; split_ifs <;> assumption
  · intro i x; split_ifs
    · exact hrθ x
    · exact hrχ x
  · intro i; split_ifs <;> assumption
  · intro i; split_ifs
    · exact hsθ.trans (ball_subset_ball (by linarith))
    · exact hsχ
  · intro i hi; simpa only [ite_eq_left hi] using hsθ
  · intro i; split_ifs
    · exact hpθ
    · exact (closedBall_subset_closedBall (by linarith : ρ / 4 ≤ ρ / 2)).trans hpχ
  · intro i hi; simpa only [ite_eq_right (by omega : ¬i.val < 2)] using hpχ

namespace CanonicalFactorWeights

variable {c : CanonicalPhase V} {ρ : ℝ} (w : CanonicalFactorWeights c ρ)

/-- The actual closed physical support of all four weights, including their
shoulders (`app:ch_regular:thm:no-return`). -/
def physicalSupport : Set (ℝ × V) := ⋃ i, tsupport (w.base i)

/-- The whole physical-frequency source product used by these factors
(`app:ch_regular:defn:protected-saturation`). -/
def sourceProduct : Set (CanonicalPhase V) := w.physicalSupport ×ˢ tsupport w.frequency

/-- All four closed supports form a compact physical source
(`app:ch_regular:thm:no-return`). -/
theorem isCompact_physicalSupport : IsCompact w.physicalSupport :=
  isCompact_iUnion w.base_compact

/-- The whole actual source product, including its boundary, is compact
(`app:ch_regular:defn:protected-saturation`). -/
theorem isCompact_sourceProduct : IsCompact w.sourceProduct :=
  w.isCompact_physicalSupport.prod w.frequency_compact

/-- The actual source product fits inside the inner canonical rectangle
(`app:ch_regular:thm:no-return`). -/
theorem sourceProduct_subset (hρ : 0 ≤ ρ) : w.sourceProduct ⊆ closedBall c ρ := by
  rintro z ⟨hx, hη⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [← closedBall_prod_same]
  exact ⟨ball_subset_closedBall (w.base_support i hi),
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall (w.frequency_support hη))⟩

/-- Both source and target weights have their entire closed support in the
plateau of either integral weight (`app:ch_regular:thm:no-return`). -/
theorem support_subset_integral_plateau {i j : Fin 4}
    (hi : i.val < 2) (hj : 2 ≤ j.val) :
    tsupport (w.base i) ⊆ interior {x | w.base j x = 1} :=
  (w.inner_support i hi).trans (ball_subset_closedBall.trans (w.integral_plateau j hj))

/-- Multiplication by either integral weight is exactly the identity on each
source or target weight, including their shoulders
(`app:ch_regular:thm:no-return`). -/
theorem integral_mul_base {i j : Fin 4} (hi : i.val < 2) (hj : 2 ≤ j.val)
    (x : ℝ × V) : w.base j x * w.base i x = w.base i x := by
  by_cases hx : w.base i x = 0
  · simp [hx]
  · have hone : x ∈ {y | w.base j y = 1} :=
      interior_subset (w.support_subset_integral_plateau hi hj (subset_tsupport _ hx))
    rw [hone, one_mul]

/-- Each actual localized weight has its whole closed phase-space support in
the complete product used by protection (`app:ch_regular:thm:no-return`). -/
theorem tsupport_localized_base_subset (i : Fin 4) :
    tsupport (fun z : CanonicalPhase V ↦ w.base i z.1 * w.frequency z.2) ⊆
      w.sourceProduct := by
  apply closure_minimal _ w.isCompact_sourceProduct.isClosed
  intro z hz
  have hh := mul_ne_zero_iff.mp hz
  exact ⟨mem_iUnion.mpr ⟨i, subset_tsupport _ hh.1⟩, subset_tsupport _ hh.2⟩

/-- The localized weights have a common plateau on the inner quarter
rectangle (`app:ch_regular:thm:no-return`). -/
theorem localized_base_eq_one (i : Fin 4) {z : CanonicalPhase V}
    (hz : z ∈ closedBall c (ρ / 4)) : w.base i z.1 * w.frequency z.2 = 1 := by
  rw [← closedBall_prod_same] at hz
  rw [interior_subset (w.base_plateau i hz.1),
    interior_subset (w.frequency_plateau hz.2), mul_one]

/-- The complete retarded image stays in the actual source product, in either
orientation. Exact covector preservation controls every output shoulder
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem completeImage_subset (backward : Bool) {K : Set (CanonicalPhase V)}
    (hK : K ⊆ w.sourceProduct) :
    completeImage backward w.physicalSupport K ⊆ w.sourceProduct := by
  rintro q ⟨hq, p, hp, hrel⟩
  exact ⟨hq, hrel.covector_eq.symm ▸ (hK hp).2⟩

/-- One uniform margin removes the fixed lower and upper endpoint jumps of
all four weights. The margin is a fixed fraction of the selected rectangle
width (`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem endpoint_buffers (i : Fin 4) (s : ℝ) (y : V) :
    (s ≤ c.1.1 - 2 * ρ + ρ → w.base i (s, y) = 0) ∧
    (c.1.1 + 2 * ρ - ρ ≤ s → w.base i (s, y) = 0) := by
  have hmem (h : w.base i (s, y) ≠ 0) : |s - c.1.1| < ρ := by
    have hm := w.base_support i (subset_tsupport _ h)
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hm
    simpa only [Real.dist_eq] using hm.1
  constructor
  · intro hs
    by_contra hn
    have hh := (abs_lt.mp (hmem hn)).1
    linarith
  · intro hs
    by_contra hn
    have hh := (abs_lt.mp (hmem hn)).2
    linarith

/-- The actual lower operator has the complete half-space kernel with the
constructed input and output weights; the endpoint is removed by the proved
buffer, not discarded (`app:ch_regular:lem:finite-chain`). -/
theorem lower_eq_kernel (hρ : 0 < ρ) (f : ℝ × V → ℂ)
    (t : ℝ) (y : V) (ht : c.1.1 - 2 * ρ ≤ t) :
    JanetCartan.Retarded.lower (c.1.1 - 2 * ρ) (w.base 2) (w.base 3) f (t, y) =
      ∫ s, lowerKernel (w.base 3) (w.base 2) t s y * f (s, y) :=
  lower_eq_integral_kernel _ ρ hρ _ _ (fun s y ↦ (w.endpoint_buffers 2 s y).1) f t y ht

/-- The literal adjoint uses the same weights in exchanged positions and the
reversed time orientation (`app:ch_regular:lem:finite-chain`). -/
theorem upper_eq_kernel (hρ : 0 < ρ) (f : ℝ × V → ℂ)
    (t : ℝ) (y : V) (ht : t ≤ c.1.1 + 2 * ρ) :
    JanetCartan.Retarded.upper (c.1.1 + 2 * ρ) (w.base 2) (w.base 3) f (t, y) =
      ∫ s, upperKernel (w.base 3) (w.base 2) t s y * f (s, y) :=
  upper_eq_integral_kernel _ ρ hρ _ _ (fun s y ↦ (w.endpoint_buffers 3 s y).2) f t y ht

end CanonicalFactorWeights

/-- Choose the four weights on an already selected finite rectangle cover.
Every point of the full source lies in source and target plateaus. This keeps
the centers selected by the retained chart construction unchanged in
`exists_constructed_signed_protection` (`app:ch_regular:thm:no-return`). -/
theorem exists_canonicalFactorWeights_cover [FiniteDimensional ℝ V]
    {S : Set (CanonicalPhase V)} (centers : Finset S) {ρ : ℝ} (hρ : 0 < ρ)
    (hcover : S ⊆ ⋃ q ∈ centers, ball q.1 (ρ / 8)) :
    ∃ w : (q : centers) → CanonicalFactorWeights q.1.1 ρ,
      ∀ z ∈ S, ∃ q : centers,
        (w q).base 0 z.1 * (w q).frequency z.2 = 1 ∧
        (w q).base 1 z.1 * (w q).frequency z.2 = 1 := by
  classical
  let w (q : centers) : CanonicalFactorWeights q.1.1 ρ :=
    Classical.choice (exists_canonicalFactorWeights q.1.1 hρ)
  refine ⟨w, ?_⟩
  intro z hz
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp (hcover hz)
  have hin : z ∈ closedBall q.1 (ρ / 4) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hzq
  exact ⟨⟨q, hq⟩, (w ⟨q, hq⟩).localized_base_eq_one 0 hin,
    (w ⟨q, hq⟩).localized_base_eq_one 1 hin⟩

end JanetCartan.ProtectedFlow
