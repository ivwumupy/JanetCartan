module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CanonicalRelations
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Complete canonical rectangles in the retained comparison charts

For `app:ch_regular:thm:no-return`, the whole compact inverse-chart image has
a finite cover by inner rectangles whose doubled closed rectangles stay in
the original chart and have physical images inside the protection ball.
The finite-family theorem chooses one common width across the retained
charts for a fixed current symbol. Uniform selection over the low coefficient
neighborhood and assembly of the finite response factors remain separate
obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover FiniteChain.Retarded

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/-- The canonical rearrangement is continuous; no new flow is selected
(`app:ch_regular:thm:no-return`). -/
theorem continuous_canonicalFlowLift : Continuous (canonicalFlowLift (V := V)) :=
  continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)

/-- The retained chart and an open physical region give an open canonical
region in which entire rectangles can be chosen
(`app:ch_regular:thm:no-return`). -/
theorem isOpen_canonical_chart_region {H : HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonFlow H V} (C : ProjectionChart Φ)
    {W : Set (Euclidean n)} (hW : IsOpen W) :
    IsOpen (canonicalFlowLift ⁻¹' C.source ∩
      (fun z ↦ (canonicalState Φ z).1) ⁻¹' W) := by
  have hpos : ContinuousOn Φ.position C.source := by
    intro z hz
    have ha := C.source_admissible z hz
    exact (Φ.position_derivative z.1 ha.1 z.2 ha.2).continuousAt.continuousWithinAt
  exact (hpos.comp continuous_canonicalFlowLift.continuousOn (fun _ hz ↦ hz)).isOpen_inter_preimage
    (C.isOpen_source.preimage continuous_canonicalFlowLift) hW

/-- A complete compact canonical source in the retained chart has a positive
physical buffer. The image is formed before choosing its buffer
(`app:ch_regular:thm:no-return`). -/
theorem exists_canonical_physical_buffer {H : HomogeneousSymbol (Euclidean n)}
    {Φ : HamiltonFlow H V} (C : ProjectionChart Φ)
    {K : Set (CanonicalPhase V)} (hK : IsCompact K)
    (hKS : MapsTo canonicalFlowLift K C.source)
    {W : Set (Euclidean n)} (hW : IsOpen W)
    (hKW : ∀ z ∈ K, (canonicalState Φ z).1 ∈ W) :
    ∃ ε > (0 : ℝ), ∀ z ∈ K, closedBall (canonicalState Φ z).1 ε ⊆ W := by
  have hpos : ContinuousOn Φ.position C.source := by
    intro z hz
    have ha := C.source_admissible z hz
    exact (Φ.position_derivative z.1 ha.1 z.2 ha.2).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun z ↦ (canonicalState Φ z).1) K :=
    hpos.comp continuous_canonicalFlowLift.continuousOn hKS
  let f : CanonicalPhase V → Euclidean n := fun z ↦ (canonicalState Φ z).1
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hc
  have himageW : f '' K ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact hKW z hz
  obtain ⟨ε, hε, hb⟩ := himage.exists_cthickening_subset_open hW himageW
  refine ⟨ε, hε, ?_⟩
  intro z hz w hw
  exact hb (closedBall_subset_cthickening (E := f '' K) (mem_image_of_mem f hz) ε hw)

namespace PhaseCover.ComparisonChart

variable {H : HomogeneousSymbol (Euclidean n)} {g : ComparisonGeometry (Euclidean n)}
    (C : ComparisonChart H g)

/-- The entire compact physical-parameter source expressed in the retained
canonical coordinates, including all boundaries
(`app:ch_regular:thm:no-return`). -/
def canonicalSource (r : ℝ) : Set (CanonicalPhase g.tangentSpace) :=
  (fun z ↦ (C.chart.coordinates z, z.2)) '' (closedBall (0 : Euclidean n) r ×ˢ g.parameters)

/-- The inverse-chart source is the actual comparison graph in physical
phase space, including its covector. This identifies the source used by the
canonical factors with the graph used by protection
(`app:ch_regular:thm:no-return`). -/
theorem canonicalState_coordinates {z : Euclidean n × (ℝ × g.tangentSpace)}
    (hz : z ∈ g.domain) :
    canonicalState C.flow (C.chart.coordinates z, z.2) = (z.1, C.gradientMap z.2 z.1) := by
  apply Prod.ext
  · exact C.chart.right_inverse z (C.target_contains hz)
  · exact (C.gradient_eq_chartMomentum hz).symm

/-- Compactness of the actual canonical source follows from the smooth
retained inverse chart on the whole product
(`app:ch_regular:thm:no-return`). -/
theorem isCompact_canonicalSource {r : ℝ} (hr : r ≤ 2 * g.radius) :
    IsCompact (C.canonicalSource r) := by
  have hsub : closedBall (0 : Euclidean n) r ×ˢ g.parameters ⊆ C.chart.target := by
    intro z hz
    exact C.target_contains (g.outer_product_subset_domain
      ⟨closedBall_subset_closedBall hr hz.1, hz.2⟩)
  exact ((isCompact_closedBall _ _).prod g.isCompact_parameters).image_of_continuousOn
    ((C.coordinates_smooth.continuousOn.mono hsub).prodMk continuousOn_snd)

/-- Inverse-chart identities put the complete canonical source in the actual
chart, with its physical position equal to the original source position
(`app:ch_regular:thm:no-return`). -/
theorem canonicalSource_mem {r : ℝ} (hr : r ≤ 2 * g.radius)
    {q : CanonicalPhase g.tangentSpace} (hq : q ∈ C.canonicalSource r) :
    canonicalFlowLift q ∈ C.chart.source ∧
      (canonicalState C.flow q).1 ∈ closedBall 0 r := by
  obtain ⟨z, hz, rfl⟩ := hq
  have ht := C.target_contains (g.outer_product_subset_domain
    ⟨closedBall_subset_closedBall hr hz.1, hz.2⟩)
  exact ⟨C.chart.maps_to_source z ht, by
    change C.flow.position (chartLift C.chart.coordinates z) ∈ closedBall 0 r
    rw [C.chart.right_inverse z ht]
    exact hz.1⟩

/-- Construct a finite cover of the *entire* canonical source by inner
rectangles, with doubled closed rectangles in the original source chart and
all their physical flow images in the protection ball. Any prescribed positive
width cap can be imposed. No containment or finite cover is assumed
(`app:ch_regular:thm:no-return`). -/
theorem exists_factor_rectangles {r τ : ℝ} (hr : 0 < r)
    (hgr : r ≤ 2 * g.radius) (hτ : 0 < τ) :
    ∃ ρ > (0 : ℝ), ρ < τ ∧
      ∃ centers : Finset (C.canonicalSource r),
        C.canonicalSource r ⊆ ⋃ q ∈ centers, ball q.1 (ρ / 8) ∧
        (∀ q : C.canonicalSource r, ∀ z ∈ closedBall q.1 (2 * ρ),
          canonicalFlowLift z ∈ C.chart.source ∧
            (canonicalState C.flow z).1 ∈ ball 0 (2 * r)) ∧
        ∃ εx > (0 : ℝ), ∀ q : C.canonicalSource r,
          ∀ z ∈ closedBall q.1 (2 * ρ),
            closedBall (canonicalState C.flow z).1 εx ⊆ ball 0 (2 * r) := by
  classical
  let O := canonicalFlowLift ⁻¹' C.chart.source ∩
    (fun z ↦ (canonicalState C.flow z).1) ⁻¹' ball 0 (2 * r)
  have hO : IsOpen O := isOpen_canonical_chart_region C.chart isOpen_ball
  have hKO : C.canonicalSource r ⊆ O := by
    intro q hq
    have hm := C.canonicalSource_mem hgr hq
    exact ⟨hm.1, closedBall_subset_ball (by linarith) hm.2⟩
  have hK := C.isCompact_canonicalSource hgr
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  let ρ := min (ε / 4) (τ / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (half_pos hτ)
  have hρε : 2 * ρ ≤ ε := by have := min_le_left (ε / 4) (τ / 2); dsimp [ρ]; linarith
  have hρτ : ρ < τ := (min_le_right _ _).trans_lt (half_lt_self hτ)
  have hcover : C.canonicalSource r ⊆ ⋃ q : C.canonicalSource r, ball q.1 (ρ / 8) := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (by positivity)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun q : C.canonicalSource r ↦ ball q.1 (ρ / 8)) (fun _ ↦ isOpen_ball) hcover
  have hfull : cthickening (2 * ρ) (C.canonicalSource r) ⊆ O :=
    (cthickening_mono hρε _).trans hεO
  obtain ⟨εx, hεx, hbuffer⟩ := exists_canonical_physical_buffer C.chart hK.cthickening
    (fun _ hz ↦ (hfull hz).1) isOpen_ball (fun _ hz ↦ (hfull hz).2)
  refine ⟨ρ, hρ, hρτ, s, hs, ?_, εx, hεx, ?_⟩
  · intro q z hz
    exact hfull (closedBall_subset_cthickening q.2 (2 * ρ) hz)
  · intro q z hz
    exact hbuffer z (closedBall_subset_cthickening q.2 (2 * ρ) hz)

end PhaseCover.ComparisonChart

/-- Source, target and either integral weight may use these same smooth
physical and covector masks. Their *closed* product support lies strictly in
the inner half of the rectangle, with a plateau on the quarter rectangle
(`app:ch_regular:thm:no-return`). -/
theorem exists_factor_rectangle_masks [FiniteDimensional ℝ V]
    (c : CanonicalPhase V) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ θ ν : (ℝ × V) → ℝ,
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ν ∧
      (∀ x, θ x ∈ Icc (0 : ℝ) 1) ∧ (∀ η, ν η ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport θ ∧ HasCompactSupport ν ∧
      tsupport θ ⊆ ball c.1 (ρ / 2) ∧ tsupport ν ⊆ ball c.2 (ρ / 2) ∧
      closedBall c.1 (ρ / 4) ⊆ interior {x | θ x = 1} ∧
      closedBall c.2 (ρ / 4) ⊆ interior {η | ν η = 1} ∧
      tsupport (fun z : CanonicalPhase V ↦ θ z.1 * ν z.2) ⊆ closedBall c (ρ / 2) ∧
      ∀ z ∈ closedBall c (ρ / 4), θ z.1 * ν z.2 = 1 := by
  obtain ⟨θ, hθ, hrθ, hcθ, hsθ, hpθ⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_closedBall c.1 (ρ / 4)) isOpen_ball (closedBall_subset_ball (by linarith : ρ / 4 < ρ / 2))
  obtain ⟨ν, hν, hrν, hcν, hsν, hpν⟩ := CompatibleResponse.exists_compact_family_cutoff
    (isCompact_closedBall c.2 (ρ / 4)) isOpen_ball (closedBall_subset_ball (by linarith : ρ / 4 < ρ / 2))
  refine ⟨θ, ν, hθ, hν, hrθ, hrν, hcθ, hcν, hsθ, hsν, hpθ, hpν, ?_, ?_⟩
  · apply closure_minimal _ isClosed_closedBall
    intro z hz
    have hh : θ z.1 ≠ 0 ∧ ν z.2 ≠ 0 := mul_ne_zero_iff.mp hz
    rw [← closedBall_prod_same]
    exact ⟨ball_subset_closedBall (hsθ (subset_tsupport _ hh.1)),
      ball_subset_closedBall (hsν (subset_tsupport _ hh.2))⟩
  · intro z hz
    rw [← closedBall_prod_same] at hz
    rw [interior_subset (hpθ hz.1), interior_subset (hpν hz.2), mul_one]

namespace PhaseCover.ComparisonChart

/-- A finite retained chart family admits one common canonical width.  The
compact source of each chart is covered by inner rectangles of that width,
all doubled rectangles stay in the chart and in the physical protection ball,
and the source/target mask pair is available on every selected centre.
The current symbol is fixed before this width is chosen; uniformity in a
coefficient neighborhood is a separate obligation
(`app:ch_regular:thm:no-return`). -/
theorem exists_common_width_factor_rectangles {I : Type*} [Finite I]
    {H : HomogeneousSymbol (Euclidean n)}
    {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart H (g i))
    {r τ : ℝ} (hr : 0 < r) (hradius : ∀ i, r ≤ 2 * (g i).radius) (hτ : 0 < τ) :
    ∃ ρ > (0 : ℝ), ρ < τ ∧
      ∀ i, ∃ centers : Finset ((C i).canonicalSource r),
        (C i).canonicalSource r ⊆ ⋃ q ∈ centers, ball q.1 (ρ / 8) ∧
        (∀ q : (C i).canonicalSource r, ∀ z ∈ closedBall q.1 (2 * ρ),
          canonicalFlowLift z ∈ (C i).chart.source ∧
            (canonicalState (C i).flow z).1 ∈ ball 0 (2 * r)) ∧
        (∃ εx > (0 : ℝ), ∀ q : (C i).canonicalSource r,
          ∀ z ∈ closedBall q.1 (2 * ρ),
            closedBall (canonicalState (C i).flow z).1 εx ⊆ ball 0 (2 * r)) ∧
        (∀ q ∈ centers, ∃ θ ν : (ℝ × (g i).tangentSpace) → ℝ,
          ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ν ∧
          (∀ x, θ x ∈ Icc (0 : ℝ) 1) ∧ (∀ η, ν η ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport θ ∧ HasCompactSupport ν ∧
          tsupport θ ⊆ ball q.1.1 (ρ / 2) ∧
          tsupport ν ⊆ ball q.1.2 (ρ / 2) ∧
          closedBall q.1.1 (ρ / 4) ⊆ interior {x | θ x = 1} ∧
          closedBall q.1.2 (ρ / 4) ⊆ interior {η | ν η = 1} ∧
          tsupport (fun z : CanonicalPhase (g i).tangentSpace ↦ θ z.1 * ν z.2) ⊆
            closedBall q.1 (ρ / 2) ∧
          ∀ z ∈ closedBall q.1 (ρ / 4), θ z.1 * ν z.2 = 1) := by
  classical
  have hex (i : I) := (C i).exists_factor_rectangles hr (hradius i) hτ
  choose widths hwidths _hcaps _centers _hcovers hfull buffers hbuffers hbuffer using hex
  obtain ⟨a, ha, hamin⟩ := (Set.finite_range widths).isCompact.exists_forall_le'
    continuous_id.continuousOn (by rintro _ ⟨i, rfl⟩; exact hwidths i)
  let ρ := min a (τ / 2)
  have hρ : 0 < ρ := lt_min ha (half_pos hτ)
  refine ⟨ρ, hρ, (min_le_right _ _).trans_lt (half_lt_self hτ), ?_⟩
  intro i
  have hρi : ρ ≤ widths i := (min_le_left _ _).trans (hamin _ (mem_range_self i))
  have hcover : (C i).canonicalSource r ⊆
      ⋃ q : (C i).canonicalSource r, ball q.1 (ρ / 8) := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (by positivity)⟩
  obtain ⟨centers, hcenters⟩ := ((C i).isCompact_canonicalSource (hradius i)).elim_finite_subcover
    (fun q : (C i).canonicalSource r ↦ ball q.1 (ρ / 8))
    (fun _ ↦ isOpen_ball) hcover
  refine ⟨centers, hcenters, ?_, ⟨buffers i, hbuffers i, ?_⟩, ?_⟩
  · intro q z hz
    exact hfull i q z (closedBall_subset_closedBall (by linarith : 2 * ρ ≤ 2 * widths i) hz)
  · intro q z hz
    exact hbuffer i q z (closedBall_subset_closedBall (by linarith : 2 * ρ ≤ 2 * widths i) hz)
  · intro q _hq
    exact exists_factor_rectangle_masks q.1 hρ

end PhaseCover.ComparisonChart
end JanetCartan.ProtectedFlow
