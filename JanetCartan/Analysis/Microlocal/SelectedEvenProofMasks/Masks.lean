module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ProtectedShoulders
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Nested
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Margins

/-!
# Uniform even physical and canonical masks for the same actual relation

Construct the proof masks on the reflected unit-mask whole-segment relation.
Its protected shoulders are proved from the original root primitives and the
same normalized pencil, rather than assumed. The actual relation and physical
operators are retained as given. Both literal orientations, full diagonal,
source buffer, annular carrier and all-order grades survive simultaneously.
Consumer: selected-sector initialization and the real restriction factors in
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ}

/-- Choose the frequency annulus of all even proof masks before the radial
proof refinement. The closed shoulders from the scaled comparison graph
are the input to the same cutoff selection; this permits matching the
comparable kernel's phase band without changing any proof mask afterwards
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_even_nested_physicalDirectLocalizers_with_prior_annulus
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (hSsym : ∀ p ∈ S, physicalCovectorReflection p ∈ S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {r M c C Lx κ Δ ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) (hC : 0 < C) (hLx : 0 ≤ Lx)
    (hκ : 0 < κ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) (N : ℕ) :
    ∃ a > (0 : ℝ), ∃ b > a,
    ∀ {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (_ : ∀ j, 0 ≤ G j),
      ∃ (θ Rbase : ℝ) (H : ℕ → ℝ),
      0 < θ ∧ 0 < Rbase ∧ (∀ k, 0 ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsCompact (U j)) → (∀ j, IsCompact (K j)) → IsClosed W →
        (∀ j, U j ⊆ D j) → (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
      ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ k y ξ, m k (y, -ξ) = m k (y, ξ)) ∧
          (∀ k, IsBufferedLocalizer (m k)
            (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt
            (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val) ⊆
              interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆
            (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
              physicalProtectedRegion Γ) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
              closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k j, IsBufferedLocalizer
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
              (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
          (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
          (∀ k j l p, ‖iteratedFDeriv ℝ l
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W
              (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ p q →
                closedBall q θ ⊆ interior {p | m k.succ p = 1}) := by
  obtain ⟨a, ha, b, hab, h⟩ :=
    exists_reflectedProofRelation_closed_shoulders_with_prior_annulus hS hB hΓ
      hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
  refine ⟨a, ha, b, hab, ?_⟩
  intro J _ ℓ η₀ εroot G hG
  obtain ⟨δ, hδ, B', hB', _, hprop⟩ := h ℓ η₀ εroot G hG
  obtain ⟨R₀, hR₀⟩ := hB'.exists_bound_of_continuousOn continuous_id.continuousOn
  let Rbase := max R₀ 0 + 1
  have hbaseBall : B' ⊆ closedBall 0 Rbase := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact (hR₀ x hx).trans ((le_max_left R₀ 0).trans (le_add_of_nonneg_right zero_le_one))
  obtain ⟨H, hH, hcut⟩ := exists_uniform_even_bufferedReachableAt_localizers
    (hB'.prod (PhysicalShells.isCompact_frequencyAnnulus a b)) hδ N
  refine ⟨δ / 8, Rbase, H, by positivity, by positivity, hH, ?_⟩
  intro Q hQ hQM i h Φ U K D W χsource χout hU hK hWclosed hUD hKD hW
    hD hh hroot hprimitive hbase hgap z Rflow rFlow T hflow htime hUflow
    I g charts hgr hderiv hnorm hcover hbuffer
  let R := physicalDirectRelation i h Φ U K W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
  let Ractual := physicalDirectRelation i h Φ U K W χsource χout Δ
  have hactual n : reachableAt Ractual S n ⊆ reachableAt (reflectedProofRelation R) S n :=
    (physicalDirectRelation_reachableAt_subset_unit_masks i h Φ U K W χsource χout Δ S n).trans
      (reachableAt_subset_reflectedProofRelation R S n)
  have hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2} := by
    apply isCompact_physicalDirectRelation i h Φ U K D W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
      hU hK hWclosed hUD hKD (fun j ↦ (hh j).continuousOn)
    intro j
    apply (hflow j).continuous.mono
    intro v hv
    exact ⟨hUflow j hv.1, ⟨by linarith [hv.2.1, htime j], hv.2.2.trans (htime j).le⟩⟩
  have hp := (hprop δ hδ.le le_rfl).2 Q hQ hQM i h Φ U K D W (fun _ _ ↦ 1) (fun _ _ ↦ 1)
    hU hK hWclosed hUD hKD hW hD hh hroot hprimitive hbase hgap
    z Rflow rFlow T hflow htime hUflow I g charts hgr hderiv hnorm hcover hbuffer
  obtain ⟨m, hsmooth, hrange, hcompact, heven, hplateau, hsupp, hshoulder, hjet, hnest⟩ :=
    hcut R S hR hS hSsym (fun n hn p hp' ↦
      (hp n hn (self_subset_cthickening _ hp')).1)
  have hbound k : cthickening (δ / 8) (tsupport (m k)) ⊆
      (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
        physicalProtectedRegion Γ := by
    intro p hp'
    obtain ⟨hb, hg⟩ := hp k.val (by omega) (hshoulder k hp')
    exact ⟨⟨hbaseBall hb.1, hb.2⟩, hg⟩
  have hreachable k : cthickening (δ / 8) (reachableAt Ractual S k.val) ⊆
      interior {p | m k p = 1} :=
    (cthickening_subset_of_subset _ ((hactual k.val).trans
      (reachableAt_subset_bufferedReachableAt (reflectedProofRelation R) S δ k.val))).trans
      (hplateau k)
  have hm k : IsBufferedLocalizer (m k) (reachableAt Ractual S k.val)
      (physicalProtectedRegion Γ) :=
    ⟨hsmooth k, hrange k, hcompact k,
      fun p hp' ↦ (hbound k (self_subset_cthickening _ hp')).2,
      fun p hp' ↦ hreachable k (self_subset_cthickening _ hp')⟩
  have hfirst : cthickening (δ / 8) (tsupport (m 0)) ⊆ V :=
    (hshoulder 0).trans (hprop δ hδ.le le_rfl).1
  refine ⟨m, heven, hm, ⟨hsmooth 0, hrange 0, hcompact 0,
    fun p hp' ↦ hfirst (self_subset_cthickening _ hp'),
    fun p hp' ↦ hplateau 0 (self_subset_cthickening _ hp')⟩,
    hfirst, hreachable, hbound, hjet, ?_, ?_, ?_, ?_, ?_⟩
  · intro k p hp' q hpq
    exact hnest k p hp' q (hpq.imp_right (fun h ↦ Or.inl (physicalDirectRelation_subset_unit_masks h)))
  · exact fun k j ↦ IsBufferedLocalizer.canonicalProofLocalizer (coordinateSplit (i j)) (hm k)
  · intro k j
    exact canonicalProofLocalizer_support_bounds (i j)
      (fun p hp' ↦ (hbound k (self_subset_cthickening _ hp')).1)
  · intro k j l p
    rw [norm_iteratedFDeriv_canonicalProofLocalizer]
    exact hjet k l _
  · intro k p hp' q hpq
    exact hnest k p hp' q (hpq.imp_right Or.inl)

/-- Construct even nested masks from the original primitive root/flow
controls and SAME comparison geometry. All constants precede the varying
field and history. The closed input shoulders propagate to closed output
balls for the actual relation and the larger unit-mask whole-segment relation.
The initial source buffer is unchanged. Canonical symbols are literal
pullbacks, and retain the physical annulus and every derivative constant.

The symmetric source is the signed physical product; `SourceGeometry`
provides its symmetry and the necessary buffer compatibility. This theorem
constructs the masks and protection, without an assumed successful chain,
mask family, reflected-chart relation or derivative-gap conclusion
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_even_nested_physicalDirectLocalizers
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    (hSsym : ∀ p ∈ S, physicalCovectorReflection p ∈ S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {r M c C Lx κ Δ ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) (hC : 0 < C) (hLx : 0 ≤ Lx)
    (hκ : 0 < κ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) (N : ℕ) :
    ∃ (θ a b Rbase : ℝ) (H : ℕ → ℝ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ (∀ k, 0 ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsCompact (U j)) → (∀ j, IsCompact (K j)) → IsClosed W →
        (∀ j, U j ⊆ D j) → (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
      ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ k y ξ, m k (y, -ξ) = m k (y, ξ)) ∧
          (∀ k, IsBufferedLocalizer (m k)
            (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt
            (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val) ⊆
              interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆
            (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
              physicalProtectedRegion Γ) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
              closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k j, IsBufferedLocalizer
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
              (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
          (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
          (∀ k j l p, ‖iteratedFDeriv ℝ l
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W
              (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ p q →
                closedBall q θ ⊆ interior {p | m k.succ p = 1}) := by
  obtain ⟨a, ha, b, hab, h⟩ :=
    exists_uniform_even_nested_physicalDirectLocalizers_with_prior_annulus hS hSsym hB hΓ
      hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
  obtain ⟨θ, Rbase, H, hθ, hmask⟩ := h ℓ η₀ εroot G hG
  exact ⟨θ, a, b, Rbase, H, hθ, ha, hab, hmask⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
