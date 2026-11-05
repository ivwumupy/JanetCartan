module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.AnnularShoulders
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.UniformTransport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphShoulders
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.SourceNeighborhood

/-!
# Protected closed shoulders for mixed original and reflected steps

Apply the existing graph-defect induction to the explicitly reflected actual
relation. Compactness, zero energy, physical/annular bounds and the uniform
transport loss have all been proved for that relation from the original
primitive inputs. No invariance of the arbitrary selected chart family is used.
Consumer: the even nested proof-mask construction on the SAME actual family,
for `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ}

/-- The graph transport bound places every buffered point either near the
source or near a scaled comparison gradient. Its frequency annulus can
therefore be fixed *before the radial chart refinement*. The refinement
only affects how small the shoulder must be. This order permits choosing a
phase band for the original comparable graph covectors
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_reflectedProofRelation_closed_shoulders_with_prior_annulus
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
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
      ∃ δ > (0 : ℝ),
      ∃ B' : Set (Euclidean (d + 1)), IsCompact B' ∧ B ⊆ B' ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ → cthickening t S ⊆ V ∧
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
        ∀ n ≤ N, cthickening t
          (bufferedReachableAt (reflectedProofRelation
            (physicalDirectRelation i h Φ U K W χsource χout Δ)) S t n) ⊆
            (B' ×ˢ PhysicalShells.frequencyAnnulus a b) ∩ physicalProtectedRegion Γ := by
  obtain ⟨σ, hσ, aS, haS, bS, habS, hsourceN⟩ :=
    exists_buffered_source_neighborhood hS hsource hΩΓ hV hSV
  let α := aS / C
  let β := max α (bS / c)
  have hα : 0 < α := div_pos haS hC
  have hαβ : α ≤ β := le_max_left _ _
  have hβ : 0 < β := hα.trans_le hαβ
  let a := min aS (α*c) / 2
  let b := max bS (β*C) + 1
  have ham : 0 < min aS (α*c) := lt_min haS (mul_pos hα hc)
  have ha : 0 < a := half_pos ham
  have haS' : a < aS := (half_lt_self ham).trans_le (min_le_left _ _)
  have haG : a < α*c := (half_lt_self ham).trans_le (min_le_right _ _)
  have hbS : bS < b := (le_max_left _ _).trans_lt (lt_add_one _)
  have hbG : β*C < b := (le_max_right _ _).trans_lt (lt_add_one _)
  refine ⟨a, ha, b, haS'.trans (habS.trans hbS), ?_⟩
  intro J _ ℓ η₀ εroot G hG
  obtain ⟨L, hL, htransport⟩ := exists_uniform_reflectedProofRelation_comparison_transport
    ℓ η₀ εroot G hG (show 0 < 2 * r by positivity) hM hc hC hLx hκ hΔ hα hαβ
  obtain ⟨δ₀, hδ₀, _, _, _, _, B', hB', hBB', hcarrier⟩ :=
    exists_uniform_reflected_bufferedReachableAt_annular_carrier ℓ η₀ εroot G hG hS
      (fun p hp ↦ (hsource p hp).2.1) hB hSB hV hSV N
  obtain ⟨sB, hsB, hbaseN⟩ := hB.exists_cthickening_subset_open isOpen_ball hBball
  let E := protectedAnnularCarrier B' (α * c) (β * C) ε Γ
  have hE : IsCompact E := isCompact_protectedAnnularCarrier hB' hΓ (mul_pos hα hc) hε.le
  let O := physicalProtectedRegion Γ ∩
    (fun p : Euclidean (d+1) × Euclidean (d+1) ↦ ‖p.2‖) ⁻¹' Ioo a b
  have hO : IsOpen O := (isOpen_physicalProtectedRegion Γ).inter
    (isOpen_Ioo.preimage continuous_snd.norm)
  have hEO : E ⊆ O := fun p hp ↦ ⟨protectedAnnularCarrier_subset_protectedRegion
    (mul_pos hα hc) hε hp, haG.trans_le hp.1.2.1, hp.1.2.2.trans_lt hbG⟩
  obtain ⟨sE, hsE, hprotected⟩ := hE.exists_cthickening_subset_open hO hEO
  let A := bufferedGraphError L (1 + β * Lx) N
  have hA : 0 ≤ A := bufferedGraphError_nonneg (zero_le_one.trans hL)
    (by positivity) N
  let δ := min δ₀ (min (min σ sB / ((N : ℝ) + 1)) (sE / (A + 1)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min
    (div_pos (lt_min hσ hsB) (by positivity)) (div_pos hsE (by positivity)))
  refine ⟨δ, hδ, B', hB', hBB', ?_⟩
  intro t ht htδ
  have ht₀ : t ≤ δ₀ := htδ.trans (min_le_left _ _)
  have htN : ((N : ℝ) + 1) * t ≤ min σ sB := by
    have ht' := htδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mp ht'
    nlinarith only [this]
  have htn (n : ℕ) (hn : n ≤ N) : ((n : ℝ) + 1) * t ≤ min σ sB :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) ht).trans htN
  have htA : A * t ≤ sE := by
    have ht' := htδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp ht'
    nlinarith only [this, ht]
  refine ⟨(hcarrier t ht ht₀).1, ?_⟩
  intro Q hQ hQM i h Φ U K D W χsource χout hU hK hWclosed hUD hKD hW
    hD hh hroot hprimitive hbase hgap z Rflow rFlow T hflow htime hUflow
    I g charts hgr hderiv hnorm hcover hbuffer
  let R := reflectedProofRelation (physicalDirectRelation i h Φ U K W χsource χout Δ)
  have hR : IsCompact {pq : (Euclidean (d + 1) × Euclidean (d + 1)) ×
      (Euclidean (d + 1) × Euclidean (d + 1)) | R pq.1 pq.2} := by
    apply isCompact_reflectedProofRelation
    apply isCompact_physicalDirectRelation i h Φ U K D W χsource χout Δ
      hU hK hWclosed hUD hKD (fun j ↦ (hh j).continuousOn)
    intro j
    apply (hflow j).continuous.mono
    intro v hv
    exact ⟨hUflow j hv.1, ⟨by linarith [hv.2.1, htime j], hv.2.2.trans (htime j).le⟩⟩
  have hRB : ∀ p q, R p q → q.1 ∈ B := by
    intro p q hpq
    exact (reflectedProofRelation_base_mem_of_root_buffer hbase hpq).2
  have hball : ∀ n ≤ N, ∀ p ∈ cthickening t (bufferedReachableAt R S t n),
      p.1 ∈ ball 0 (2 * r) := by
    intro n hn p hp
    exact hbaseN (cthickening_mono ((htn n hn).trans (min_le_right _ _)) B
      (bufferedReachableAt_fst_subset hR hS hSB hRB ht n p hp))
  have hbound := (hcarrier t ht ht₀).2 i h Φ U K W χsource χout Δ hprimitive hbase
  have hestimate (η : ComparisonGeometry.ParameterFamily g) :=
    htransport Q hQ hQM i h Φ U K D W χsource χout hD hh hroot hKD hW
      (fun j v hv ↦ hprimitive j v (Or.inr hv)) hgap z Rflow rFlow T hflow htime hUflow
      (g η.1) (charts η.1) (by linarith [hgr η.1]) (hderiv η.1)
      (fun ξ hξ x hx ↦ hnorm ⟨η.1, ξ, hξ⟩ x hx) η.2.1 η.2.2
  have hstart : ∀ p ∈ cthickening (((N : ℝ) + 1) * t) S, ∀ q, R p q →
      ∃ η scale, scale ∈ Icc α β ∧
        p.2 = scale • ComparisonChart.familyGradient charts η p.1 := by
    intro p hp q hpq
    obtain ⟨_, hx, hne, hΩ, _, hlo, hup⟩ := hsourceN p
      (cthickening_mono (htN.trans (min_le_left _ _)) S hp)
    have henergy : normalizedSymbol Q p = 0 :=
      reflectedProofRelation_source_energy hKD
        (fun j v hv ↦ (hflow j).initial v (hUflow j hv))
        (fun j v hv t ht ↦ (hflow j).hasDerivAt (hUflow j hv)
          ⟨by linarith [ht.1, htime j], ht.2.trans_lt (htime j)⟩)
        (fun j v hv ↦ (hroot j v hv).2.1) hpq
    obtain ⟨η, scale, hs, heq⟩ := comparison_source_scaled_cover hQ charts hc hC hcover
      (fun η x hx ↦ hnorm η x (ball_subset_closedBall
        (ball_subset_ball (by linarith) hx))) hx hne hΩ hlo hup henergy
    exact ⟨η, scale, ⟨hs.1, hs.2.trans (le_max_right _ _)⟩, heq⟩
  have herr := bufferedReachableAt_graph_error hR hS (ComparisonChart.familyGradient charts)
    hα hαβ hL hLx ht N (fun n hn p hp ↦ ball_subset_closedBall (hball n hn p hp))
    (fun η ↦ (hestimate η).1) hstart (fun η ↦ (hestimate η).2)
  intro n hn q hq
  have hbaseq := (hbound n hn hq).1
  rcases herr n hn q hq with hsourceq | ⟨η, scale, hs, he⟩
  · obtain ⟨_, _, _, _, hprotectedq, hl, hu⟩ := hsourceN q
      (cthickening_mono ((htn n hn).trans (min_le_left _ _)) S hsourceq)
    exact ⟨⟨hbaseq, haS'.le.trans hl, hu.trans hbS.le⟩, hprotectedq⟩
  · have hscale : 0 < scale := hα.trans_le hs.1
    let v : Euclidean (d + 1) × Euclidean (d + 1) :=
      (q.1, scale • ComparisonChart.familyGradient charts η q.1)
    have hvP : v ∈ positiveConicLift (ComparisonChart.familyGradient charts)
        (ball 0 (2 * r)) univ := ⟨hball n hn q hq, η, mem_univ _, scale, hscale, rfl⟩
    have hvE : v ∈ E := by
      refine ⟨⟨(hbound n hn hq).1, ?_⟩, hbuffer v hvP⟩
      change α * c ≤ ‖scale • ComparisonChart.familyGradient charts η q.1‖ ∧
        ‖scale • ComparisonChart.familyGradient charts η q.1‖ ≤ β * C
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      obtain ⟨hlo, hup⟩ := hnorm η q.1 (ball_subset_closedBall (hball n hn q hq))
      exact ⟨mul_le_mul hs.1 hlo hc.le hscale.le,
        mul_le_mul hs.2 hup (norm_nonneg _) hβ.le⟩
    have hdist : dist q v = ‖q.2 - scale • ComparisonChart.familyGradient charts η q.1‖ := by
      change max (dist q.1 q.1)
        (dist q.2 (scale • ComparisonChart.familyGradient charts η q.1)) = _
      rw [dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    have hclose : dist q v ≤ sE := hdist ▸ he.trans ((mul_le_mul_of_nonneg_right
      (bufferedGraphError_mono hL (by positivity) hn) ht).trans htA)
    have hqO := hprotected (mem_cthickening_of_dist_le _ _ _ _ hvE hclose)
    exact ⟨⟨hbaseq, hqO.2.1.le, hqO.2.2.le⟩, hqO.1⟩


/-- A single positive shoulder width protects every finite mixture of actual
and covector-reflected steps, including full diagonal shoulders. The width,
annulus and compact base envelope precede all current coefficients and finite
histories. The SAME original roots, flows, complete segments, masks, elapsed
bound and initialized comparison charts supply every input. In particular,
protection of the reflected relation is proved from the literal normalized
symbol parity, not assumed as a mask-construction premise
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_reflectedProofRelation_closed_shoulders
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
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
    ∃ δ > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > a,
      ∃ B' : Set (Euclidean (d + 1)), IsCompact B' ∧ B ⊆ B' ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ → cthickening t S ⊆ V ∧
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
        ∀ n ≤ N, cthickening t
          (bufferedReachableAt (reflectedProofRelation
            (physicalDirectRelation i h Φ U K W χsource χout Δ)) S t n) ⊆
            (B' ×ˢ PhysicalShells.frequencyAnnulus a b) ∩ physicalProtectedRegion Γ := by
  obtain ⟨a, ha, b, hab, h⟩ :=
    exists_reflectedProofRelation_closed_shoulders_with_prior_annulus hS hB hΓ
      hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
  obtain ⟨δ, hδ, B', hp⟩ := h ℓ η₀ εroot G hG
  exact ⟨δ, hδ, a, ha, b, hab, B', hp⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
