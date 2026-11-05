module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Angular
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations

/-!
# Finite nested masks for the actual protected relations

For the protected finite-chain paragraph of `app:ch_regular:lem:finite-chain`,
compactness of the supported relation gives compact reachable sets and open
input neighborhoods controlling the complete image. Choose the masks backward
from the final protected region, so every closed shoulder is included.

The actual-relation constructor below derives its image inclusion from the
retained comparison charts in `ProtectedMasks.Angular`. Relation compactness
is the separate geometry input of `jc-protected-mask-compact-relations`.
This construction concerns one fixed family: uniform neighborhoods and symbol
bounds as the current coefficients vary remain obligations of the parent.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ}

private theorem reachableAt_zero
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) :
    reachableAt R S 0 = S := by
  ext q
  constructor
  · rintro ⟨p, hp, hc⟩
    cases hc
    exact hp
  · exact fun hq ↦ ⟨q, hq, .refl q⟩

private theorem reachableAt_one
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) :
    reachableAt R S 1 = S ∪ Prod.snd '' ({pq | R pq.1 pq.2} ∩ Prod.fst ⁻¹' S) := by
  ext q
  constructor
  · rintro ⟨p, hp, hc⟩
    cases hc with
    | tail hs hc =>
      cases hc
      rcases hs with rfl | hr
      · exact Or.inl hp
      · exact Or.inr ⟨(p, q), ⟨hr, hp⟩, rfl⟩
  · rintro (hq | ⟨⟨p, q⟩, ⟨hr, hp⟩, rfl⟩)
    · exact ⟨q, hq, .tail (Or.inl rfl) (.refl q)⟩
    · exact ⟨p, hp, .tail (Or.inr hr) (.refl q)⟩

private theorem reachableAt_succ_first
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (k : ℕ) :
    reachableAt R S (k + 1) = reachableAt R (reachableAt R S 1) k := by
  ext q
  constructor
  · rintro ⟨p, hp, hc⟩
    cases hc with
    | tail hs hc => exact ⟨_, ⟨p, hp, .tail hs (.refl _)⟩, hc⟩
  · rintro ⟨y, ⟨p, hp, hc⟩, hyq⟩
    cases hc with
    | tail hs hc =>
      cases hc
      exact ⟨p, hp, .tail hs hyq⟩

/-- Finite reachable sets, including every diagonal branch, are compact when
the actual relation graph and original source are compact. Consumer:
`exists_nested_physicalDirectLocalizers` (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_reachableAt_of_compact_relation
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2})
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (k : ℕ) : IsCompact (reachableAt R S k) := by
  induction k generalizing S with
  | zero => simpa only [reachableAt_zero] using hS
  | succ k ih =>
    rw [reachableAt_succ_first]
    apply ih
    rw [reachableAt_one]
    exact hS.union ((hR.inter_right (hS.isClosed.preimage continuous_fst)).image continuous_snd)

/- The bad input set is the first projection of a compact part of the relation.
Its complement controls ALL outputs, including at the mask shoulders.
The diagonal is imposed separately because its global graph is not compact. -/
private theorem exists_open_completeImage_neighborhood
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2})
    {S O : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hO : IsOpen O)
    (himage : ∀ p ∈ S, ∀ q, p = q ∨ R p q → q ∈ O) :
    ∃ V, IsOpen V ∧ S ⊆ V ∧
      ∀ p ∈ V, ∀ q, p = q ∨ R p q → q ∈ O := by
  let B := Prod.fst '' ({pq | R pq.1 pq.2} ∩ Prod.snd ⁻¹' Oᶜ)
  have hB : IsClosed B :=
    ((hR.inter_right (hO.isClosed_compl.preimage continuous_snd)).image continuous_fst).isClosed
  refine ⟨O ∩ Bᶜ, hO.inter hB.isOpen_compl, ?_, ?_⟩
  · intro p hp
    refine ⟨himage p hp p (Or.inl rfl), ?_⟩
    rintro ⟨⟨p', q⟩, ⟨hr, hq⟩, heq⟩
    exact hq (himage p hp q (Or.inr (heq ▸ hr)))
  · intro p hp q hpq
    rcases hpq with rfl | hr
    · exact hp.1
    · by_contra hq
      exact hp.2 ⟨(p, q), ⟨hr, hq⟩, rfl⟩

private theorem plateau_subset_tsupport (m : LocalizerSymbol (d + 1)) :
    interior {p | m p = 1} ⊆ tsupport m := by
  intro p hp
  apply subset_tsupport m
  change m p ≠ 0
  have hp' : p ∈ {p | m p = 1} := interior_subset hp
  rw [show m p = 1 from hp']
  exact one_ne_zero

/- Purely topological backward construction. Only this private deduction
accepts a whole-chain image inclusion. The public constructor proves it from
the SAME retained source cover and comparison charts using Angular. -/
private theorem exists_nested_relationLocalizers
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2}) (N : ℕ)
    {S B O : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hS : IsCompact S) (hB : IsOpen B) (hSB : S ⊆ B) (hO : IsOpen O)
    (himage : reachableAt R S N ⊆ O) :
    ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
      (∀ j, IsBufferedLocalizer (m j) (reachableAt R S j.val) O) ∧
      tsupport (m 0) ⊆ B ∧
      ∀ j : Fin N, ∀ p ∈ tsupport (m j.castSucc), ∀ q,
        p = q ∨ R p q → q ∈ interior {q | m j.succ q = 1} := by
  induction N generalizing S B with
  | zero =>
    rw [reachableAt_zero] at himage
    obtain ⟨m, hm, hr, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
      hS (hB.inter hO) (subset_inter hSB himage)
    refine ⟨fun _ ↦ m, ?_, fun p hp ↦ (hs hp).1, ?_⟩
    · intro j
      have hj : j.val = 0 := by omega
      rw [hj, reachableAt_zero]
      exact ⟨hm, hr, hc, fun p hp ↦ (hs hp).2, hp⟩
    · exact Fin.elim0
  | succ N ih =>
    have hS₁ := isCompact_reachableAt_of_compact_relation hR hS 1
    have himage₁ : reachableAt R (reachableAt R S 1) N ⊆ O := by
      rwa [← reachableAt_succ_first]
    obtain ⟨ms, hms, _, hnest⟩ := ih hS₁ isOpen_univ (subset_univ _) himage₁
    have hp₁ : reachableAt R S 1 ⊆ interior {q | ms 0 q = 1} := by
      simpa only [Fin.val_zero, reachableAt_zero] using (hms 0).plateau
    obtain ⟨V, hV, hSV, hmap⟩ := exists_open_completeImage_neighborhood hR
      isOpen_interior (fun p hp q hpq ↦ hp₁ ⟨p, hp, .tail hpq (.refl q)⟩)
    have hSO : S ⊆ O := by
      intro p hp
      exact (hms 0).support_subset (plateau_subset_tsupport _
        (hp₁ ⟨p, hp, .tail (Or.inl rfl) (.refl p)⟩))
    obtain ⟨m, hm, hr, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff
      hS ((hB.inter hO).inter hV) (subset_inter (subset_inter hSB hSO) hSV)
    refine ⟨Fin.cons m ms, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simpa only [Fin.cons_zero, Fin.val_zero, reachableAt_zero] using
          (show IsBufferedLocalizer m S O from
            ⟨hm, hr, hc, fun p hp ↦ (hs hp).1.2, hp⟩)
      · rw [Fin.cons_succ, Fin.val_succ, reachableAt_succ_first]
        exact hms j
    · simpa only [Fin.cons_zero] using
        (show tsupport m ⊆ B from fun p hp ↦ (hs hp).1.1)
    · intro j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using
          (fun p hp q hpq ↦ hmap p (hs hp).2 q hpq :
            ∀ p ∈ tsupport m, ∀ q, p = q ∨ R p q → q ∈ interior {q | ms 0 q = 1})
      · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hnest j

/-- Smooth compact proof masks for every fixed number of actual direct factors,
including depth zero. The initial closed support lies in the prescribed source
buffer; each complete diagonal/relation image of a closed support lies in the
next open plateau. All masks are in physical coordinates, and the final closed
support has positive lower and finite upper normalized frequency bounds.

Protection is deduced from `physicalDirectRelation_chain_angular_buffer` with
its literal common pencil, roots, flow, whole domains, and SAME retained
comparison charts/source cover. The sole additional relation geometry input is
compactness of the supported graph, produced independently by
`jc-protected-mask-compact-relations`. This is for one fixed family; uniformity
in varying current coefficients is not asserted
(`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph). -/
theorem exists_nested_physicalDirectLocalizers {I J : Type*}
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q)
    (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
        ((coordinateSplit (i j)).symm (h j v, v.2.2))
        ((coordinateSplit (i j)).symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean (d + 1))}
    (C : (j : I) → ComparisonChart
      (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j))
    {r ε : ℝ} (hradius : ∀ j, 2 * r < (g j).radius)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    {G : Set (Euclidean (d + 1))}
    (hcover : ∀ z ∈ S, normalizedSymbol Q z = 0 →
      z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hbuffer : ∀ z ∈ positiveConicLift (ComparisonChart.familyGradient C)
      (ball 0 (2 * r)) univ, closedBall (normalizedCovector z.2) ε ⊆ G)
    (hretained : ∀ z ∈ S, ∀ w k,
      PositiveConicChain (CompleteCharacteristicSegment
        (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (ball 0 (2 * r)))
        z w k → closedBall (normalizedCovector w.2) ε ⊆ G)
    (hε : 0 < ε) (hS : IsCompact S) (hSnonzero : ∀ z ∈ S, z.2 ≠ 0)
    {Bsource : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hBsource : IsOpen Bsource) (hSBsource : S ⊆ Bsource)
    (hcompact : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) |
      physicalDirectRelation i h Φ U K (ball 0 (2 * r)) χsource χout Δ pq.1 pq.2})
    (N : ℕ) :
    ∃ (m : Fin (N + 1) → LocalizerSymbol (d + 1))
      (Bfinal : Set (Euclidean (d + 1))) (a b : ℝ),
      (∀ j, IsBufferedLocalizer (m j)
        (reachableAt (physicalDirectRelation i h Φ U K (ball 0 (2 * r)) χsource χout Δ)
          S j.val) (physicalProtectedRegion G)) ∧
      IsBufferedLocalizer (m 0) S Bsource ∧
      (∀ j : Fin N, ∀ p ∈ tsupport (m j.castSucc), ∀ q,
        p = q ∨ physicalDirectRelation i h Φ U K (ball 0 (2 * r)) χsource χout Δ p q →
        q ∈ interior {q | m j.succ q = 1}) ∧
      IsCompact Bfinal ∧ 0 < a ∧ a < b ∧
      tsupport (m (Fin.last N)) ⊆ Bfinal ×ˢ PhysicalShells.frequencyAnnulus a b := by
  have hprotected :
      reachableAt (physicalDirectRelation i h Φ U K (ball 0 (2 * r)) χsource χout Δ)
        S N ⊆ physicalProtectedRegion G := by
    rintro w ⟨z, hz, hc⟩
    have hang := physicalDirectRelation_chain_angular_buffer i hQ h Φ U K D χsource χout Δ
      hKD hi hode hD hh hroot C hradius hcover hbuffer hretained hz hc
    refine ⟨physicalDirectRelation_chain_covector_ne_zero i h Φ U K D _ χsource χout Δ
      hKD hi hode (fun j v hv ↦ (hroot j v hv).1) hc (hSnonzero z hz), ?_⟩
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (closedBall_mem_nhds _ hε) hang)
  obtain ⟨m, hm, hsource, hnest⟩ := exists_nested_relationLocalizers hcompact N
    hS hBsource hSBsource (isOpen_physicalProtectedRegion G) hprotected
  obtain ⟨Bfinal, a, b, hBfinal, ha, hab, hsupport⟩ :=
    EvolutionLocalization.exists_elapsed_localizer_annular_carrier (hm (Fin.last N))
      (fun _ hp ↦ hp.1)
  have hfirst : IsBufferedLocalizer (m 0) S Bsource := by
    have hm₀ := hm 0
    rw [Fin.val_zero, reachableAt_zero] at hm₀
    exact ⟨hm₀.smooth, hm₀.range, hm₀.compactSupport, hsource, hm₀.plateau⟩
  exact ⟨m, Bfinal, a, b, hm, hfirst, hnest, hBfinal, ha, hab, hsupport⟩

/-- Assemble the finite masks from the actual finite-family primitive buffers.
The closed whole-segment carrier lies inside the SAME retained comparison ball;
compactness is proved from the original root and flow continuity, and angular
protection is proved from the original common pencil. No compact relation,
whole-chain image inclusion or successful mask is assumed. Both orientations,
full diagonal shoulders, the source buffer and the original elapsed interval
are retained, including depth zero (`app:ch_regular:lem:finite-chain`).

`UniformGeometry.exists_uniform_fieldRoot_conicGeometry` supplies the smooth
roots, actual flows and compact root buffers; initialized signed protection
supplies `C`, `hcover`, `hbuffer`, and `hretained`. Selecting these SAME objects
for the actual current family remains the arbitrary-accuracy parent's task.
The conclusion here concerns each fixed family, not uniform symbol constants
over varying coefficients. -/
theorem exists_nested_physicalDirectLocalizers_of_primitive_buffers {I J : Type*} [Finite J]
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q)
    (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
        ((coordinateSplit (i j)).symm (h j v, v.2.2))
        ((coordinateSplit (i j)).symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean (d + 1))}
    (C : (j : I) → ComparisonChart
      (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j))
    {r ε : ℝ} (hradius : ∀ j, 2 * r < (g j).radius)
    (hWball : W ⊆ ball 0 (2 * r))
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    {G : Set (Euclidean (d + 1))}
    (hcover : ∀ z ∈ S, normalizedSymbol Q z = 0 →
      z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hbuffer : ∀ z ∈ positiveConicLift (ComparisonChart.familyGradient C)
      (ball 0 (2 * r)) univ, closedBall (normalizedCovector z.2) ε ⊆ G)
    (hretained : ∀ z ∈ S, ∀ w k,
      PositiveConicChain (CompleteCharacteristicSegment
        (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (ball 0 (2 * r)))
        z w k → closedBall (normalizedCovector w.2) ε ⊆ G)
    (hε : 0 < ε) (hS : IsCompact S) (hSnonzero : ∀ z ∈ S, z.2 ≠ 0)
    {Bsource : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hBsource : IsOpen Bsource) (hSBsource : S ⊆ Bsource)
    (hU : ∀ j, IsCompact (U j)) (hK : ∀ j, IsCompact (K j))
    (hW : IsClosed W) (hUD : ∀ j, U j ⊆ D j)
    (hΦ : ∀ j, ContinuousOn (Φ j) (U j ×ˢ Icc 0 Δ))
    (N : ℕ) :
    ∃ (m : Fin (N + 1) → LocalizerSymbol (d + 1))
      (Bfinal : Set (Euclidean (d + 1))) (a b : ℝ),
      (∀ j, IsBufferedLocalizer (m j)
        (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ)
          S j.val) (physicalProtectedRegion G)) ∧
      IsBufferedLocalizer (m 0) S Bsource ∧
      (∀ j : Fin N, ∀ p ∈ tsupport (m j.castSucc), ∀ q,
        p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        q ∈ interior {q | m j.succ q = 1}) ∧
      IsCompact Bfinal ∧ 0 < a ∧ a < b ∧
      tsupport (m (Fin.last N)) ⊆ Bfinal ×ˢ PhysicalShells.frequencyAnnulus a b := by
  have hcompact := isCompact_physicalDirectRelation i h Φ U K D W χsource χout Δ
    hU hK hW hUD hKD (fun j ↦ (hh j).continuousOn) hΦ
  have hprotected :
      reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ)
        S N ⊆ physicalProtectedRegion G := by
    rintro w ⟨z, hz, hc⟩
    have hang := physicalDirectRelation_chain_angular_buffer i hQ h Φ U K D χsource χout Δ
      hKD hi hode hD hh hroot C hradius hcover hbuffer hretained hz
      (physicalDirectRelation_chain_mono_physical_buffer hWball hc)
    refine ⟨physicalDirectRelation_chain_covector_ne_zero i h Φ U K D _ χsource χout Δ
      hKD hi hode (fun j v hv ↦ (hroot j v hv).1) hc (hSnonzero z hz), ?_⟩
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (closedBall_mem_nhds _ hε) hang)
  obtain ⟨m, hm, hsource, hnest⟩ := exists_nested_relationLocalizers hcompact N
    hS hBsource hSBsource (isOpen_physicalProtectedRegion G) hprotected
  obtain ⟨Bfinal, a, b, hBfinal, ha, hab, hsupport⟩ :=
    EvolutionLocalization.exists_elapsed_localizer_annular_carrier (hm (Fin.last N))
      (fun _ hp ↦ hp.1)
  have hfirst : IsBufferedLocalizer (m 0) S Bsource := by
    have hm₀ := hm 0
    rw [Fin.val_zero, reachableAt_zero] at hm₀
    exact ⟨hm₀.smooth, hm₀.range, hm₀.compactSupport, hsource, hm₀.plateau⟩
  exact ⟨m, Bfinal, a, b, hm, hfirst, hnest, hBfinal, ha, hab, hsupport⟩

/-- The masks constructed above also buffer the literal source-recut relation.
The source remains on the original `χ₃ = 1` plateau. Consumer: recut complete
residual factors in `app:ch_regular:lem:finite-chain`; no new source domain or
orientation convention is introduced. -/
theorem sourceRecutRelation_mem_nested_plateau
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {N : ℕ} {m : Fin (N + 1) → LocalizerSymbol (d + 1)}
    (hnest : ∀ j : Fin N, ∀ p ∈ tsupport (m j.castSucc), ∀ q,
      p = q ∨ R p q → q ∈ interior {q | m j.succ q = 1})
    {χ₂ χ₃ : Euclidean (d + 1) → ℝ} (hcut : EqOn χ₃ 1 (tsupport χ₂))
    (j : Fin N) {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ tsupport (m j.castSucc)) (hpq : sourceRecutRelation χ₂ R p q) :
    χ₃ p.1 = 1 ∧ q ∈ interior {q | m j.succ q = 1} :=
  ⟨sourceRecutRelation_outer_eq_one hcut hpq, hnest j p hp q hpq.2⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
