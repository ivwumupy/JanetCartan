module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.IncidenceMasks

/-!
# Incidence masks inside the same retained leading cells

Select a compatible leading cell for each frozen incidence root BEFORE the
local supported masks are chosen. Any subsequent positive mask widths admit a
finite sphere cover retaining those cell choices and the full detector Gram
inequality. The cells are produced by `RetainedCover.Finite` or its history
variant. This supplies the incidence-center membership required by
`exists_carrier_in_retained_leading_cell_before_geometry` without identifying
independently chosen leading witnesses (`app:ch_background:defn:bg-row`).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.ActualComparison

/-- Choose the retained leading-cell index before any local mask shrinking,
then obtain a finite incidence cover inside those SAME cells and mask plateaus.
The original Gram estimate is retained on each whole neighborhood. Consumer:
the finite assembly of `exists_carrier_in_retained_leading_cell_before_geometry`
(`app:ch_background:defn:bg-row`, `app:ch_seed:eq:seed-frozen-detection`). -/
theorem exists_retained_incidence_cell_selection {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (I : (b : Fin D.chartCount) → Fin (D.patchCount b) → Type*)
    (E : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      I b a → Set (Euclidean n × CarrierParameter))
    (hE : ∀ b a j, IsOpen (E b a j))
    (hcover : ∀ b a z, z ∈ parameterCube (D.patches b a).radius →
      ∃ j, ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈ E b a j) :
    ∃ cell : (p : IncidenceCenter D) → (a : Fin (D.patchCount p.1.1)) → I p.1.1 a,
      (∀ p a, ((0 : Euclidean n),
        (D.roots p.1.1 a p.1.2 0, spectatorCenter (D.roots p.1.1 a p.1.2))) ∈
          E p.1.1 a (cell p a)) ∧
    ∀ (r w : (p : IncidenceCenter D) → Fin (D.patchCount p.1.1) → ℝ)
      (hr : ∀ p a, 0 < r p a) (hw : ∀ p a, 0 < w p a),
    ∃ centers : Finset (IncidenceCenter D), ∃ ε : centers → ℝ,
      (∀ j, 0 < ε j) ∧
      sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (ε j) ∧
      (∀ j, ball j.1.1.2 (ε j) ⊆ D.domain j.1.1.1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (ε j), ∀ a : Fin (D.patchCount j.1.1.1),
        ((0 : Euclidean n), (D.roots j.1.1.1 a q 0,
          spectatorCenter (D.roots j.1.1.1 a q))) ∈ E j.1.1.1 a (cell j.1 a) ∧
        angularMask (D.roots j.1.1.1 a j.1.1.2)
          (NormedSpace.normalize ((T j.1.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint j.1.1.2))
          (hr j.1 a) (hw j.1 a)
          (D.roots j.1.1.1 a q 0, spectatorCenter (D.roots j.1.1.1 a q))
          (NormedSpace.normalize ((T j.1.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (ε j), ∀ s : Euclidean n,
        c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
          ∑ a, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 a).toFun
            (D.roots j.1.1.1 a q))) s ^ 2) := by
  classical
  have hroot (p : IncidenceCenter D) (a : Fin (D.patchCount p.1.1)) :
      D.roots p.1.1 a p.1.2 ∈ parameterCube (D.patches p.1.1 a).radius :=
    fun i ↦ ((hD.2.2.2.2.1 p.1.1 a).2.2.1 p.1.2 p.2.2).1 i |>.le
  choose cell hcell using fun p a ↦ hcover p.1.1 a _ (hroot p a)
  refine ⟨cell, hcell, ?_⟩
  intro r w hr hw
  have hlocal (p : IncidenceCenter D) : ∃ ε > 0,
      ball p.1.2 ε ⊆ D.domain p.1.1 ∧ ∀ q ∈ ball p.1.2 ε, ∀ a,
        ((0 : Euclidean n), (D.roots p.1.1 a q 0,
          spectatorCenter (D.roots p.1.1 a q))) ∈ E p.1.1 a (cell p a) ∧
        angularMask (D.roots p.1.1 a p.1.2)
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint p.1.2))
          (hr p a) (hw p a) (D.roots p.1.1 a q 0, spectatorCenter (D.roots p.1.1 a q))
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1 := by
    have hk : p.1.2 ≠ 0 := by
      intro hh
      have hs := p.2.1
      simp [hh] at hs
    choose ε hε hdomain hmask using fun a ↦ exists_incidence_mask_neighborhood
      (hD.2.2.2.2.1 p.1.1 a).1 (T p.1.1 a) (hD.2.2.1 p.1.1)
      (hD.2.2.2.2.1 p.1.1 a).2 hk p.2.2 (hr p a) (hw p a)
    have hall : ∀ᶠ q in 𝓝 p.1.2, ∀ a,
        ((0 : Euclidean n), (D.roots p.1.1 a q 0,
          spectatorCenter (D.roots p.1.1 a q))) ∈ E p.1.1 a (cell p a) ∧
        angularMask (D.roots p.1.1 a p.1.2)
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint p.1.2))
          (hr p a) (hw p a) (D.roots p.1.1 a q 0, spectatorCenter (D.roots p.1.1 a q))
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1 := by
      rw [Filter.eventually_all]
      intro a
      have hrootcont := (hD.2.2.2.2.1 p.1.1 a).2.1.continuousOn.continuousAt
        ((hD.2.2.1 p.1.1).mem_nhds p.2.2)
      have hcarrier : Continuous (fun z : Euclidean 3 ↦
          ((0 : Euclidean n), (z 0, spectatorCenter z))) := by
        unfold spectatorCenter
        fun_prop
      exact Filter.Eventually.and ((hcarrier.continuousAt.comp hrootcont).preimage_mem_nhds
        ((hE _ _ _).mem_nhds (hcell p a)))
          (Filter.mem_of_superset (ball_mem_nhds _ (hε a)) (fun q hq ↦ hmask a q hq))
    obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff_ball.mp
      (Filter.Eventually.and ((hD.2.2.1 p.1.1).mem_nhds p.2.2) hall)
    exact ⟨δ, hδ, fun q hq ↦ (hδall q hq).1, fun q hq ↦ (hδall q hq).2⟩
  choose ε hε hdomain hmask using hlocal
  have hcover : sphere (0 : Euclidean n) 1 ⊆
      ⋃ p : IncidenceCenter D, ball p.1.2 (ε p) := by
    intro k hk
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hD.2.2.2.1 hk)
    exact mem_iUnion.mpr ⟨⟨(b, k), hk, hb⟩, mem_ball_self (hε _)⟩
  obtain ⟨centers, hcenters⟩ := (isCompact_sphere (0 : Euclidean n) 1).elim_finite_subcover
    (fun p : IncidenceCenter D ↦ ball p.1.2 (ε p)) (fun _ ↦ isOpen_ball) hcover
  refine ⟨centers, fun j ↦ ε j.1, fun j ↦ hε j.1, ?_,
    fun j ↦ hdomain j.1, fun j ↦ hmask j.1, ?_⟩
  · intro k hk
    obtain ⟨j, hj, hkj⟩ := mem_iUnion₂.mp (hcenters hk)
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hkj⟩
  · intro j q hq s
    exact hD.2.2.2.2.2 j.1.1.1 q (hdomain j.1 hq) s

end JanetCartan.ContinuumRow.CanonicalConic
