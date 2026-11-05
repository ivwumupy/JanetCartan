module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.UniformGeometry
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FactorRectangles

/-!
# Fixed finite canonical rectangles for the actual comparison cover

The comparison-phase and complete-rectangle construction in
`app:ch_regular:thm:no-return`. The local producer proves quantitative bounds
for the retained charts by root, ODE and inverse uniqueness. Finite minima and
compactness then choose centers, widths and physical buffers before the
variable symbol. The finite family is allowed to be empty.

This leaf imports the canonical-factor consumer. It is deliberately not
imported by `PhaseCover`, since that would create a cycle through the existing
canonical relations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual finite comparison cover with fixed canonical rectangles
(`app:ch_regular:thm:no-return`, comparison-phase paragraph).

For every prescribed smaller positive source radius and time-width cap, the
scalar C³ threshold, common width, finite centers and positive physical buffer
are chosen before the current symbol. The same retained charts satisfy all
regular-graph bounds and cover every current characteristic point of the
original complete source product. Their entire canonical images of the
smaller product are covered by the inner balls, and every doubled closed
rectangle stays in the retained chart with a common closed physical buffer.
No rectangle coverage, continuity estimate or buffer is an input.

For Euclidean physical space the displayed source image is definitionally
`ComparisonChart.canonicalSource`. The `UniformWeights` adapter constructs the
four weights at these fixed centers, and
`CanonicalFactorWeights.completeImage_has_buffered_segments` consumes these
same buffered rectangles. No frequency, high norm or accuracy enters their selection. -/
theorem exists_finite_comparison_cover_with_uniform_rectangles
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hhom₀ : H₀.ConicHomogeneous)
    (hfrozen : ∀ z ∈ D, H₀.h z = H₀.h (0, z.2))
    {Ω G M : Set E} (hΩ : IsCompact Ω)
    (hsource : ({0} : Set E) ×ˢ Ω ⊆ D)
    (hΩzero : ∀ p ∈ Ω, p ≠ 0)
    (htransverse : ∀ p ∈ Ω, H₀.h (0, p) = 0 → H₀.hp (0, p) ≠ 0)
    (hG : IsOpen G) (hM : IsClosed M)
    (hregular : ∀ p ∈ Ω, normalizedCovector p ∈ G \ M) :
    ∃ (s : Finset {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0})
      (g : s → ComparisonGeometry E) (r δ c C ε : ℝ) (K : Set (E × E)) (A : Set E),
      0 < r ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      IsCompact K ∧ K ⊆ D ∧ closedBall (0 : E) (3 * r) ×ˢ Ω ⊆ K ∧
      (∀ i : s, 3 * r < (g i).radius) ∧
      IsCompact A ∧ A ⊆ G \ M ∧ (∀ q ∈ A, closedBall q ε ⊆ G \ M) ∧
      ∀ r' : ℝ, 0 < r' → r' ≤ r → ∀ τ : ℝ, 0 < τ →
        ∃ (d ρ εx : ℝ) (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace)),
          0 < d ∧ d ≤ δ ∧ 0 < ρ ∧ ρ < τ ∧ 0 < εx ∧
          ∀ (H : HomogeneousSymbol E), D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
            H.ConicHomogeneous → cNorm K 3 (fun z ↦ H.h z - H₀.h z) ≤ d →
            ∃ charts : (i : s) → ComparisonChart H (g i),
              (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
                c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
                  ‖ComparisonChart.familyGradient charts η x‖ ≤ C ∧
                  normalizedCovector (ComparisonChart.familyGradient charts η x) ∈ A) ∧
              (∀ x ∈ closedBall 0 r, ∀ p ∈ Ω, H.h (x, p) = 0 →
                ∃ η : ComparisonGeometry.ParameterFamily g,
                  p = ComparisonChart.familyGradient charts η x) ∧
              ∀ i : s,
                (fun z ↦ ((charts i).chart.coordinates z, z.2)) ''
                    (closedBall (0 : E) r' ×ˢ (g i).parameters) ⊆
                  ⋃ q ∈ centers i, ball q (ρ / 8) ∧
                ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
                  canonicalFlowLift z ∈ (charts i).chart.source ∧
                  closedBall ((charts i).flow.position (canonicalFlowLift z)) εx ⊆
                    ball 0 (2 * r') := by
  classical
  let F (p : {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0}) :
      LocalComparisonFamily H₀ D G M p.1 :=
    Classical.choice (exists_localComparisonFamily H₀ hD hDH₀ hH₀ hhom₀
      (hΩzero p p.2.1) (hsource ⟨mem_singleton 0, p.2.1⟩) p.2.2
      (htransverse p p.2.1 p.2.2) hG hM (hregular p p.2.1))
  obtain ⟨s, r, δ, c, C, ε, K, hr, hδ, hc, hC, hε, hK, hKD, hsourceK,
    hballs, hfamily⟩ :=
    exists_finite_comparison_cover_with_selection H₀ hD hH₀ hfrozen hΩ hsource F
  have hzero : cNorm K 3 (fun z ↦ H₀.h z - H₀.h z) ≤ δ := by
    simp only [sub_self]
    exact (cNorm_zero K 3).le.trans hδ.le
  obtain ⟨_, _, hri, _, _⟩ := hfamily H₀ hDH₀ hH₀ hhom₀ hzero
  obtain ⟨A, hA, hAG, hAbuffer, hAcontains⟩ :=
    exists_compact_regular_directions (G := G) (M := M) hε
  refine ⟨s, fun i ↦ (F i.1).geometry, r, δ, c, C, ε / 2, K, A,
    hr, hδ, hc, hC, half_pos hε, hK, hKD, hsourceK, hri, hA, hAG, hAbuffer, ?_⟩
  intro r' hr' hrr τ hτ
  have hex (i : s) := (F i.1).exists_uniform_rectangle_margin hr'
    (show r' ≤ (F i.1).geometry.radius by linarith only [hrr, hri i, hr])
  choose a ha hrect using hex
  obtain ⟨a₀, ha₀, ha₀i⟩ := (finite_range a).isCompact.exists_forall_le'
    continuous_id.continuousOn (by rintro _ ⟨i, rfl⟩; exact ha i)
  let ρ := min a₀ (τ / 2)
  have hρ : 0 < ρ := lt_min ha₀ (half_pos hτ)
  have hρi (i : s) : ρ ≤ a i := (min_le_left _ _).trans (ha₀i _ (mem_range_self i))
  choose di buffers centers hdi _hdiThreshold hbuffers hrectangles using
    (fun i : s ↦ hrect i ρ hρ (hρi i))
  obtain ⟨d₀, hd₀, hd₀i⟩ := (finite_range di).isCompact.exists_forall_le'
    continuous_id.continuousOn (by rintro _ ⟨i, rfl⟩; exact hdi i)
  obtain ⟨εx, hεx, hεxi⟩ := (finite_range buffers).isCompact.exists_forall_le'
    continuous_id.continuousOn (by rintro _ ⟨i, rfl⟩; exact hbuffers i)
  let d := min δ d₀
  have hd : 0 < d := lt_min hδ hd₀
  refine ⟨d, ρ, εx, centers, hd, min_le_left _ _, hρ,
    (min_le_right _ _).trans_lt (half_lt_self hτ), hεx, ?_⟩
  intro H hHD hH hhom hsmall
  obtain ⟨charts, hselection, _hri, hbounds, hcover⟩ :=
    hfamily H hHD hH hhom (hsmall.trans (min_le_left _ _))
  refine ⟨charts, ?_, ?_, ?_⟩
  · intro η x hx
    obtain ⟨hlo, hup, hbuf⟩ := hbounds η.1 x hx η.2.1 η.2.2
    refine ⟨hlo, hup, hAcontains _ ?_ hbuf⟩
    exact norm_smul_inv_norm (norm_pos_iff.mp (hc.trans_le hlo))
  · intro x hx p hp hz
    obtain ⟨i, η, hη, he⟩ := hcover x hx p hp hz
    exact ⟨⟨i, ⟨η, hη⟩⟩, he⟩
  · intro i
    obtain ⟨hi, hchart⟩ := hselection i
    have hsmalli : cNorm (closedBall (0, i.1.1) (F i.1).stateRadius) 3
        (fun z ↦ H.h z - H₀.h z) ≤ di i := by
      apply (cNorm_mono_set_of_contDiffAt (hballs i.1 i.2) hK
        (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hKD hz))).of_le
          (by simp))).trans
      exact hsmall.trans ((min_le_right _ _).trans (hd₀i _ (mem_range_self i)))
    obtain ⟨hcov, hbuf⟩ := hrectangles i ⟨H, hHD, hH, hhom, hi⟩ hsmalli
    rw [hchart]
    refine ⟨hcov, ?_⟩
    intro q hq z hz
    obtain ⟨hs, hb⟩ := hbuf q hq z hz
    exact ⟨hs, (closedBall_subset_closedBall (hεxi _ (mem_range_self i))).trans hb⟩

end JanetCartan.ProtectedFlow.PhaseCover
