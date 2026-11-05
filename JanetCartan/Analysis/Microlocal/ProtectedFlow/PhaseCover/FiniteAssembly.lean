module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ChartData
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.ZeroExclusion
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Finite assembly from local comparison families

The compactness argument in the finite comparison-phase paragraph of
`app:ch_regular:thm:no-return`. A single compact scalar-symbol estimate set
controls all selected charts and excludes zeros outside their covector cover.
The local producer remains an explicit input here; its instantiation belongs
to the final phase-cover theorem, not to this independent deduction.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A compact angular source at the physical origin has one buffered physical
ball in the open scalar-symbol domain (`app:ch_regular:thm:no-return`). -/
theorem exists_source_product_ball {Ω : Set E} {D : Set (E × E)}
    (hΩ : IsCompact Ω) (hD : IsOpen D) (hsource : ({0} : Set E) ×ˢ Ω ⊆ D) :
    ∃ r > 0, closedBall (0 : E) r ×ˢ Ω ⊆ D := by
  obtain ⟨U, V, hU, _, h0U, hΩV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hΩ hD hsource
  obtain ⟨r, hr, hball⟩ :=
    nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  exact ⟨r, hr, fun _ hz ↦ hUV ⟨hball hz.1, hΩV hz.2⟩⟩

/-- Select finitely many actual local comparison families and one scalar C³
threshold. Coverage holds for every current characteristic source point,
including points not on the frozen zero set. The fixed compact estimate set
contains both the whole source product and each selected construction ball.
Uniform graph bounds hold on the entire common outer physical ball.

This is the compactness deduction for `app:ch_regular:thm:no-return`, conditional
on local families. `LocalConstruction.exists_localComparisonFamily` must supply
`F` from the primitive scalar symbol before this proves the requested finite
phase construction. No finite-cover assumption is used. -/
theorem exists_finite_comparison_cover_with_selection
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hfrozen : ∀ z ∈ D, H₀.h z = H₀.h (0, z.2))
    {Ω G M : Set E} (hΩ : IsCompact Ω)
    (hsource : ({0} : Set E) ×ˢ Ω ⊆ D)
    (F : (p : {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0}) →
      LocalComparisonFamily H₀ D G M p.1) :
    ∃ (s : Finset {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0})
      (r δ c C ε : ℝ) (K : Set (E × E)),
      0 < r ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      IsCompact K ∧ K ⊆ D ∧ closedBall (0 : E) (3 * r) ×ˢ Ω ⊆ K ∧
      (∀ i ∈ s, closedBall (0, i.1) (F i).stateRadius ⊆ K) ∧
      ∀ (H : HomogeneousSymbol E) (hHD : D ⊆ H.domain)
        (hH : ContDiffOn ℝ ∞ H.h D) (hhom : H.ConicHomogeneous),
        cNorm K 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ charts : (i : s) → ComparisonChart H (F i.1).geometry,
          (∀ i : s, ∃ hi : cNorm (closedBall (0, i.1.1) (F i.1).stateRadius) 3
              (fun z ↦ H.h z - H₀.h z) ≤ (F i.1).threshold,
            charts i = (F i.1).charts ⟨H, hHD, hH, hhom, hi⟩) ∧
          (∀ i : s, 3 * r < (F i.1).geometry.radius) ∧
          (∀ i : s, ∀ x ∈ closedBall 0 (2 * r), ∀ η ∈ (F i.1).geometry.parameters,
            c ≤ ‖(charts i).gradientMap η x‖ ∧ ‖(charts i).gradientMap η x‖ ≤ C ∧
            closedBall (normalizedCovector ((charts i).gradientMap η x)) ε ⊆ G \ M) ∧
          ∀ x ∈ closedBall 0 r, ∀ p ∈ Ω, H.h (x, p) = 0 →
            ∃ i : s, ∃ η ∈ (F i.1).geometry.parameters, p = (charts i).gradientMap η x := by
  classical
  have hf : ContinuousOn (fun p ↦ H₀.h (0, p)) Ω :=
    hH₀.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ hsource ⟨mem_singleton 0, hp⟩)
  obtain ⟨s, d, hd, _, hcover⟩ := exists_finite_stable_zero_cover (X := E) hΩ hf
    (fun i ↦ (F i).covectors) (fun i ↦ (F i).covectors_open)
    (fun p hp hz ↦ ⟨⟨p, hp, hz⟩, (F ⟨p, hp, hz⟩).center_mem⟩)
  obtain ⟨r₀, hr₀, hsourceD⟩ := exists_source_product_ball hΩ hD hsource
  obtain ⟨r₁, c, C, hr₁, _, hc, hC, hcommon⟩ :=
    ActualCarriers.exists_common_phase_buffers
      (fun i : s ↦ (F i.1).geometry.radius)
      (fun i : s ↦ min (F i.1).threshold (min (F i.1).lower (F i.1).angularBuffer))
      (fun i : s ↦ (F i.1).upper)
      (fun i ↦ (F i.1).geometry.radius_pos)
      (fun i ↦ lt_min (F i.1).threshold_pos
        (lt_min (F i.1).lower_pos (F i.1).angularBuffer_pos))
  let r := min r₀ r₁ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : 3 * r < r₀ := by
    have hh := min_le_left r₀ r₁
    dsimp [r]
    linarith
  have hrr₁ : r < r₁ := by
    have hh := min_le_right r₀ r₁
    dsimp [r]
    linarith
  have hri (i : s) : 3 * r < (F i.1).geometry.radius := by
    have hh := (hcommon i).1
    linarith
  let δ := min (d / 2) c
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  let K := (closedBall (0 : E) r₀ ×ˢ Ω) ∪ ⋃ i ∈ s, closedBall (0, i.1) (F i).stateRadius
  have hK : IsCompact K :=
    ((isCompact_closedBall _ _).prod hΩ).union
      (s.finite_toSet.isCompact_biUnion (fun i _ ↦ isCompact_closedBall _ _))
  have hKD : K ⊆ D := by
    apply union_subset hsourceD
    exact iUnion_subset (fun i ↦ iUnion_subset (fun _ ↦ (F i).state_subset))
  have hballs (i) (hi : i ∈ s) : closedBall (0, i.1) (F i).stateRadius ⊆ K := by
    intro z hz
    exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩)
  have hsourceK : closedBall (0 : E) (3 * r) ×ˢ Ω ⊆ K := fun _ hz ↦
    Or.inl ⟨closedBall_subset_closedBall hrr₀.le hz.1, hz.2⟩
  refine ⟨s, r, δ, c, C, c, K, hr, hδ, hc, hC, hc, hK, hKD, hsourceK, hballs, ?_⟩
  intro H hHD hH hhom hsmall
  have hlocal (i : s) : cNorm (closedBall (0, i.1.1) (F i.1).stateRadius) 3
      (fun z ↦ H.h z - H₀.h z) ≤ (F i.1).threshold := by
    apply (cNorm_mono_set_of_contDiffAt (hballs i.1 i.2) hK
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))).trans
    exact hsmall.trans ((min_le_right _ _).trans ((hcommon i).2.1.trans (min_le_left _ _)))
  let symbols (i : s) : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
      H.ConicHomogeneous ∧ cNorm (closedBall (0, i.1.1) (F i.1).stateRadius) 3
        (fun z ↦ H.h z - H₀.h z) ≤ (F i.1).threshold} :=
    ⟨H, hHD, hH, hhom, hlocal i⟩
  let charts (i : s) : ComparisonChart H (F i.1).geometry := (F i.1).charts (symbols i)
  refine ⟨charts, fun i ↦ ⟨hlocal i, rfl⟩, hri, ?_, ?_⟩
  · intro i x hx η hη
    have hxi : x ∈ closedBall 0 (2 * (F i.1).geometry.radius) :=
      closedBall_subset_closedBall (by have hh := hri i; linarith) hx
    obtain ⟨hlo, hup, hgap⟩ := (F i.1).regular (symbols i) x hxi η hη
    have hlow : c ≤ (F i.1).lower :=
      (hcommon i).2.1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have heps : c ≤ (F i.1).angularBuffer :=
      (hcommon i).2.1.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨hlow.trans hlo, hup.trans (hcommon i).2.2,
      (closedBall_subset_closedBall heps).trans hgap⟩
  · intro x hx p hp hz
    have hclose : ∀ y ∈ closedBall (0 : E) r, ∀ q ∈ Ω,
        |H.h (y, q) - H₀.h (0, q)| < d := by
      intro y hy q hq
      have hym : (y, q) ∈ K :=
        hsourceK ⟨closedBall_subset_closedBall (by linarith) hy, hq⟩
      rw [← hfrozen (y, q) (hKD hym)]
      exact ((abs_sub_le_cNorm_on_compact hD hK hKD hH hH₀ hym).trans hsmall).trans_lt hδd
    obtain ⟨i, hi, hpO⟩ := hcover (closedBall 0 r) H.h hclose x hx p hp hz
    have hxi : x ∈ closedBall 0 (F i).geometry.radius :=
      closedBall_subset_closedBall (by have hh := hri ⟨i, hi⟩; linarith) hx
    obtain ⟨η, hη, he⟩ := (F i).covers (symbols ⟨i, hi⟩) x hxi p hpO hz
    exact ⟨⟨i, hi⟩, η, hη, he⟩


/-- The original finite graph-cover interface, retaining all its conclusions.
The stronger selection theorem also identifies every chart with its actual
local producer for the uniform rectangles (`app:ch_regular:thm:no-return`). -/
theorem exists_finite_comparison_cover_of_local
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (hfrozen : ∀ z ∈ D, H₀.h z = H₀.h (0, z.2))
    {Ω G M : Set E} (hΩ : IsCompact Ω)
    (hsource : ({0} : Set E) ×ˢ Ω ⊆ D)
    (F : (p : {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0}) →
      LocalComparisonFamily H₀ D G M p.1) :
    ∃ (s : Finset {p : E // p ∈ Ω ∧ H₀.h (0, p) = 0})
      (r δ c C ε : ℝ) (K : Set (E × E)),
      0 < r ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      IsCompact K ∧ K ⊆ D ∧ closedBall (0 : E) (3 * r) ×ˢ Ω ⊆ K ∧
      (∀ i ∈ s, closedBall (0, i.1) (F i).stateRadius ⊆ K) ∧
      ∀ (H : HomogeneousSymbol E), D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        H.ConicHomogeneous → cNorm K 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ charts : (i : s) → ComparisonChart H (F i.1).geometry,
          (∀ i : s, 3 * r < (F i.1).geometry.radius) ∧
          (∀ i : s, ∀ x ∈ closedBall 0 (2 * r), ∀ η ∈ (F i.1).geometry.parameters,
            c ≤ ‖(charts i).gradientMap η x‖ ∧ ‖(charts i).gradientMap η x‖ ≤ C ∧
            closedBall (normalizedCovector ((charts i).gradientMap η x)) ε ⊆ G \ M) ∧
          ∀ x ∈ closedBall 0 r, ∀ p ∈ Ω, H.h (x, p) = 0 →
            ∃ i : s, ∃ η ∈ (F i.1).geometry.parameters, p = (charts i).gradientMap η x := by
  obtain ⟨s, r, δ, c, C, ε, K, hr, hδ, hc, hC, hε, hK, hKD, hsourceK,
    hballs, hfamily⟩ :=
    exists_finite_comparison_cover_with_selection H₀ hD hH₀ hfrozen hΩ hsource F
  refine ⟨s, r, δ, c, C, ε, K, hr, hδ, hc, hC, hε, hK, hKD, hsourceK, hballs, ?_⟩
  intro H hHD hH hhom hsmall
  obtain ⟨charts, _hselection, hri, hbounds, hcover⟩ := hfamily H hHD hH hhom hsmall
  exact ⟨charts, hri, hbounds, hcover⟩

end JanetCartan.ProtectedFlow.PhaseCover
