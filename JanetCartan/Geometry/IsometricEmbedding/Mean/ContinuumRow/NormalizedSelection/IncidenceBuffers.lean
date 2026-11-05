module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.IncidenceMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Radius

/-!
# Incidence masks inside fixed source-flow buffers

Apply the retained incidence-cover theorem only after the local source-flow
buffer and conic widths have been selected. A common measurement radius then
works on the entire closed mask support for every contracting source scale.
The original detector Gram inequality holds on the same finite cover.
Consumer: the common finite family assembled from
`NormalizedSelection.exists_retained_source_carrier_integrals`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open FullPhaseCharts.ActualComparison

/-- Shrink only the incidence/spectator width so that its entire compact
parameter support stays inside the supplied source-flow buffer. The upper
width may come from the retained conic constructor; no carrier labels or
measure are changed (`app:ch_background:defn:bg-row`, `new:lem:scaling`). -/
theorem exists_carrierSupport_in_parameter_ball (z₀ : Euclidean 3)
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∃ r > 0, r ≤ a ∧ MapsTo parameter (carrierSupport z₀ (r := r)) (ball z₀ ε) := by
  have heq : parameter (z₀ 0, spectatorCenter z₀) = z₀ := by
    simp only [parameter_apply, carrierParameters_spectatorCenter]
  have hnhds := ((isOpen_ball.preimage parameter.continuous).mem_nhds
    (show (z₀ 0, spectatorCenter z₀) ∈ parameter ⁻¹' ball z₀ ε by
      simpa only [mem_preimage, heq] using mem_ball_self hε))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let r := min δ a
  have hr : 0 < r := lt_min hδ ha
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro z hz
  apply hδsub
  have hball : z ∈ closedBall (z₀ 0, spectatorCenter z₀) (r / 2) := by
    rw [← closedBall_prod_same]
    exact hz
  exact closedBall_subset_ball (by dsimp [r]; linarith [min_le_left δ a]) hball

/-- One finite cover, one mask family and one measurement radius inside the
supplied local source-flow buffers. All choices precede every source scale.
The direction widths and their centers are exactly those supplied by the
retained conic construction, and the original full detector Gram estimate is
retained on each covering neighborhood. The compact support, including its
boundary, stays inside the flow buffer under every `σ ∈ [0,1]`
(`app:ch_background:defn:bg-row`, `app:ch_seed:eq:seed-frozen-detection`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_incidence_masks_with_common_source_buffer
    {n : ℕ} {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (G : FlatReference n)
    (ε a w : (p : IncidenceCenter D) → Fin (D.patchCount p.1.1) → ℝ)
    (hε : ∀ p l, 0 < ε p l) (ha : ∀ p l, 0 < a p l) (hw : ∀ p l, 0 < w p l) :
    ∃ r : (p : IncidenceCenter D) → Fin (D.patchCount p.1.1) → ℝ,
    ∃ hr : ∀ p l, 0 < r p l,
      (∀ p l, r p l ≤ a p l ∧ MapsTo parameter
        (carrierSupport (D.roots p.1.1 l p.1.2) (r := r p l))
        (ball (D.roots p.1.1 l p.1.2) (ε p l))) ∧
    ∃ centers : Finset (IncidenceCenter D), ∃ εcover : centers → ℝ,
      (∀ j, 0 < εcover j) ∧
      sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j) ∧
      (∀ j, ball j.1.1.2 (εcover j) ⊆ D.domain j.1.1.1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ l : Fin (D.patchCount j.1.1.1),
        angularMask (D.roots j.1.1.1 l j.1.1.2)
          (NormedSpace.normalize ((T j.1.1.1 l).data.adapted.embedding.toContinuousLinearMap.adjoint j.1.1.2))
          (hr j.1 l) (hw j.1 l) (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))
          (NormedSpace.normalize ((T j.1.1.1 l).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
        c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
          ∑ l, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 l).toFun
            (D.roots j.1.1.1 l q))) s ^ 2) ∧
    ∃ b : ℝ, ∃ hb : 0 < b,
      6 * b < G.domain.chartRadius ∧ 6 * b < 1 / 2 ∧
      (∀ j : centers, ∀ l : Fin (D.patchCount j.1.1.1), 6 * b < r j.1 l) ∧
      ∀ σ ∈ Icc (0 : ℝ) 1, ∀ j : centers, ∀ l : Fin (D.patchCount j.1.1.1),
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (σ • p.1, parameter p.2))
          (tsupport (FixedCutoffs.physical hb 1) ×ˢ
            carrierSupport (D.roots j.1.1.1 l j.1.1.2) (r := r j.1 l))
          (ball (0 : Euclidean n) (ε j.1 l) ×ˢ
            ball (D.roots j.1.1.1 l j.1.1.2) (ε j.1 l)) := by
  classical
  choose r hr hra hsupp using fun p l ↦
    exists_carrierSupport_in_parameter_ball (D.roots p.1.1 l p.1.2) (hε p l) (ha p l)
  obtain ⟨centers, εcover, hεcover, hcover, hdomain, hmask, hgram⟩ :=
    exists_finite_incidence_mask_cover hD T r w hr hw
  let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
  obtain ⟨b, hb, hbG, hbhalf, hsmall⟩ := CommonMeasurement.exists_common_radius G
    (fun i : ι ↦ min (r i.1.1 i.2) (ε i.1.1 i.2))
    (fun i ↦ lt_min (hr i.1.1 i.2) (hε i.1.1 i.2))
  refine ⟨r, hr, fun p l ↦ ⟨hra p l, hsupp p l⟩,
    centers, εcover, hεcover, hcover, hdomain, hmask, hgram,
    b, hb, hbG, hbhalf, fun j l ↦ (hsmall ⟨j, l⟩).trans_le (min_le_left _ _), ?_⟩
  intro σ hσ j l p hp
  refine ⟨?_, hsupp j.1 l hp.2⟩
  have hsize : 6 * b < ε j.1 l := (hsmall ⟨j, l⟩).trans_le (min_le_right _ _)
  have hx : p.1 ∈ ball (0 : Euclidean n) (ε j.1 l) :=
    closedBall_subset_ball (by linarith : 4 * b < ε j.1 l)
      (FixedCutoffs.physical_tsupport_four hb 1 hp.1)
  exact (convex_ball (0 : Euclidean n) (ε j.1 l)).smul_mem_of_zero_mem
    (mem_ball_self (hε j.1 l)) hx hσ

end JanetCartan.ContinuumRow.NormalizedSelection
