module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence

/-!
# Incidence coverage retained by the actual local masks

A mask of any positive local incidence and angular widths equals one near its
frozen incident direction. Compactness selects finitely many such neighborhoods
from the SAME cover and Hamilton families. Local widths may already have been
shrunk by the actual supported carrier construction. No uniform lower bound on
those widths is required, and no operator estimate is assumed.

The consuming construction is the finite family in
`exists_finite_actual_density_row` (`app:ch_background:defn:bg-row`). Actual
before-geometry local choices and matching their selected minor/flow scalars
remain separate from this compactness deduction.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.ActualComparison

/-- Any positive supported mask has a plateau along the SAME smooth incidence
section near its center. The normalized modulation direction is the actual
orthogonal projection in the retained Hamilton chart (`bg-row`, `bg-Psi`). -/
theorem exists_incidence_mask_neighborhood {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {V : Set (Euclidean n)} (hV : IsOpen V)
    {root : Euclidean n → Euclidean 3} (hsec : P.IsIncidenceSection V root c)
    {k : Euclidean n} (hk : k ≠ 0) (hkV : k ∈ V)
    {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    ∃ ε > 0, ball k ε ⊆ V ∧ ∀ q ∈ ball k ε,
      angularMask (root k)
        (NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k)) hr hw
        (root q 0, spectatorCenter (root q))
        (NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1 := by
  let L := T.data.adapted.embedding.toContinuousLinearMap.adjoint
  have hL : L k ≠ 0 := FullPhaseCharts.FrozenIncidence.tangential_direction_ne_zero
    T hP (hsec.2.1 k hkV).1 hk (hsec.2.1 k hkV).2.2.2
  have hroot : ContinuousAt root k := hsec.1.continuousOn.continuousAt (hV.mem_nhds hkV)
  have hs : ContinuousAt (fun q ↦ root q 0) k := (by fun_prop : ContinuousAt
    (fun z : Euclidean 3 ↦ z 0) (root k)).comp hroot
  have hv : ContinuousAt (fun q ↦ spectatorCenter (root q)) k := by
    have hh : Continuous (spectatorCenter : Euclidean 3 → Euclidean 2) := by
      unfold spectatorCenter
      fun_prop
    exact hh.continuousAt.comp hroot
  have hθ : ContinuousAt (fun q ↦ NormedSpace.normalize (L q)) k :=
    (L.continuous.continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr hL)).smul
      L.continuous.continuousAt
  have hplateau : ∀ᶠ q in 𝓝 k,
      q ∈ V ∧ root q 0 ∈ ball (root k 0) (r / 4) ∧
        spectatorCenter (root q) ∈ ball (spectatorCenter (root k)) (r / 4) ∧
        NormedSpace.normalize (L q) ∈ ball (NormedSpace.normalize (L k)) (w / 4) := by
    exact Filter.Eventually.and (hV.mem_nhds hkV)
      (Filter.Eventually.and (hs.preimage_mem_nhds (ball_mem_nhds _ (by positivity)))
        (Filter.Eventually.and (hv.preimage_mem_nhds (ball_mem_nhds _ (by positivity)))
          (hθ.preimage_mem_nhds (ball_mem_nhds _ (by positivity)))))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff_ball.mp hplateau
  refine ⟨ε, hε, fun q hq ↦ (he q hq).1, fun q hq ↦ ?_⟩
  exact angularMask_one _ _ hr hw (ball_subset_closedBall (he q hq).2.1)
    (ball_subset_closedBall (he q hq).2.2.1) (ball_subset_closedBall (he q hq).2.2.2)

/-- A direction in one of the retained covering charts. This is only indexing
data, before any local mask or operator is chosen (`app:ch_seed:eq:seed-frozen-detection`). -/
abbrev IncidenceCenter {n : ℕ} (D : CoverData n) :=
  {p : Fin D.chartCount × Euclidean n // p.2 ∈ sphere (0 : Euclidean n) 1 ∧ p.2 ∈ D.domain p.1}

/-- Even after independent local mask shrinkings, finitely many of the SAME
incident roots and directions cover the entire sphere, and every detector of
the selected chart has mask one on its neighborhood. The full original Gram
inequality therefore remains available there. The widths are the positive
outputs of the local supported carrier construction, not assumed operator
bounds (`app:ch_background:defn:bg-row`, `app:ch_seed:eq:seed-frozen-detection`). -/
theorem exists_finite_incidence_mask_cover {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (b : Fin D.chartCount) → (a : Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches b a) U hU)
    (r w : (p : IncidenceCenter D) → Fin (D.patchCount p.1.1) → ℝ)
    (hr : ∀ p a, 0 < r p a) (hw : ∀ p a, 0 < w p a) :
    ∃ centers : Finset (IncidenceCenter D), ∃ ε : centers → ℝ,
      (∀ j, 0 < ε j) ∧
      sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (ε j) ∧
      (∀ j, ball j.1.1.2 (ε j) ⊆ D.domain j.1.1.1) ∧
      (∀ j, ∀ q ∈ ball j.1.1.2 (ε j), ∀ a : Fin (D.patchCount j.1.1.1),
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
  have hlocal (p : IncidenceCenter D) : ∃ ε > 0,
      ball p.1.2 ε ⊆ D.domain p.1.1 ∧ ∀ q ∈ ball p.1.2 ε, ∀ a,
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
        angularMask (D.roots p.1.1 a p.1.2)
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint p.1.2))
          (hr p a) (hw p a) (D.roots p.1.1 a q 0, spectatorCenter (D.roots p.1.1 a q))
          (NormedSpace.normalize ((T p.1.1 a).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1 := by
      rw [Filter.eventually_all]
      intro a
      exact Filter.mem_of_superset (ball_mem_nhds _ (hε a)) (fun q hq ↦ hmask a q hq)
    obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff_ball.mp
      (Filter.Eventually.and ((hD.2.2.1 p.1.1).mem_nhds p.2.2) hall)
    exact ⟨δ, hδ, fun q hq ↦ (hδall q hq).1, fun q hq ↦ (hδall q hq).2⟩
  choose ε hε hdomain hmask using hlocal
  have hcover : sphere (0 : Euclidean n) 1 ⊆ ⋃ p : IncidenceCenter D, ball p.1.2 (ε p) := by
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
