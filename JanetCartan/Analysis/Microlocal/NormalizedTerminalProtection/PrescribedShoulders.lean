module

public import JanetCartan.Analysis.Microlocal.NormalizedTerminalProtection.UniformCarrier
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ProtectedShoulders

/-!
# Quantitative propagation into a prescribed common terminal mask

Refactor the graph-defect proof of the reflected closed shoulders so its target
is the plateau of a supplied final mask. The carrier and annulus precede the
mask, proof depth, radial refinement and current field. Its quantitative plateau
is produced by `exists_common_normalizedSource_terminal_localizer` on this exact
carrier; no second terminal mask is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open ProtectedMasks SelectedEvenProofMasks RegularSector.Characteristic
open ActualCarriers HamiltonPhase ProtectedFlow PhaseCover FiniteChain.Graph

variable {d : ℕ}

/-- The source margins and comparison gradients fix a terminal carrier before
any finite depth or selected root family. Every final mask with the common
closed plateau admits positive uniform shoulders for the full reflected relation.
The shoulder width precedes the current coefficient field and histories, and
retains the original masks, complete segments and elapsed bound. The supplied
plateau is exactly the output of the common normalized-source mask constructor
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_uniform_reflected_prescribed_terminal_shoulders
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B)
    {r c C ε : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ a > (0 : ℝ), ∃ b > a, ∃ εterminal > (0 : ℝ),
    ∀ (mi : LocalizerSymbol (d+1)) (δfinal : ℝ), 0 < δfinal →
      cthickening δfinal
        (protectedAnnularCarrier (cthickening 1 B) a b εterminal Γ) ⊆
          interior {p | mi p = 1} →
    ∀ (N : ℕ) {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (_ : ∀ j, 0 ≤ G j),
    ∀ {M Lx κ Δ : ℝ}, 0 ≤ M → 0 ≤ Lx → 0 < κ → 0 ≤ Δ →
      ∃ δ > (0 : ℝ),
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
            interior {p | mi p = 1} := by
  obtain ⟨σ, hσ, aS, haS, bS, habS, hsourceN⟩ :=
    exists_buffered_source_neighborhood hS hsource hΩΓ hV hSV
  obtain ⟨εS, hεS, hsourceBuffer⟩ := exists_compact_source_angular_margin hS.cthickening
    (fun p hp ↦ (hsourceN p hp).2.2.2.2.1)
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
  refine ⟨a, ha, b, haS'.trans (habS.trans hbS), min εS ε, lt_min hεS hε, ?_⟩
  intro mi δfinal hδfinal hplateau N J _ ℓ η₀ εroot G hG M Lx κ Δ hM hLx hκ hΔ
  obtain ⟨L, hL, htransport⟩ := exists_uniform_reflectedProofRelation_comparison_transport
    ℓ η₀ εroot G hG (show 0 < 2 * r by positivity) hM hc hC hLx hκ hΔ hα hαβ
  obtain ⟨sB, hsB, hbaseN⟩ := hB.exists_cthickening_subset_open isOpen_ball hBball
  let A := bufferedGraphError L (1 + β * Lx) N
  have hA : 0 ≤ A := bufferedGraphError_nonneg (zero_le_one.trans hL) (by positivity) N
  let δ := min (min σ sB / ((N : ℝ) + 1))
    (min (1 / ((N : ℝ) + 1)) (δfinal / (A + 1)))
  have hδ : 0 < δ := lt_min
    (div_pos (lt_min hσ hsB) (by positivity))
    (lt_min (by positivity) (div_pos hδfinal (by positivity)))
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have htN : ((N : ℝ) + 1) * t ≤ min σ sB := by
    have ht' := htδ.trans (min_le_left _ _)
    have := (le_div_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mp ht'
    nlinarith only [this]
  have htB : ((N : ℝ) + 1) * t ≤ 1 := by
    have ht' := htδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mp ht'
    nlinarith only [this]
  have htn (n : ℕ) (hn : n ≤ N) : ((n : ℝ) + 1) * t ≤ ((N : ℝ) + 1) * t :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) ht
  have htA : A * t ≤ δfinal := by
    have ht' := htδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp ht'
    nlinarith only [this, ht]
  refine ⟨?_, ?_⟩
  · intro p hp
    apply (hsourceN p ?_).1
    apply cthickening_mono (δ₂ := σ) _ S hp
    have hNt : t ≤ ((N : ℝ) + 1) * t := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact hNt.trans (htN.trans (min_le_left _ _))
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
  have hbaseq : ∀ n ≤ N, ∀ p ∈ cthickening t (bufferedReachableAt R S t n),
      p.1 ∈ cthickening 1 B := by
    intro n hn p hp
    exact cthickening_mono ((htn n hn).trans htB) B
      (bufferedReachableAt_fst_subset hR hS hSB hRB ht n p hp)
  have hball : ∀ n ≤ N, ∀ p ∈ cthickening t (bufferedReachableAt R S t n),
      p.1 ∈ ball 0 (2 * r) := by
    intro n hn p hp
    exact hbaseN (cthickening_mono (((htn n hn).trans htN).trans (min_le_right _ _)) B
      (bufferedReachableAt_fst_subset hR hS hSB hRB ht n p hp))
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
  rcases herr n hn q hq with hsourceq | ⟨η, scale, hs, he⟩
  · have hqS := cthickening_mono (((htn n hn).trans htN).trans (min_le_left _ _)) S hsourceq
    obtain ⟨_, _, _, _, _, hl, hu⟩ := hsourceN q hqS
    apply hplateau (self_subset_cthickening _ ?_)
    exact ⟨⟨hbaseq n hn q hq, haS'.le.trans hl, hu.trans hbS.le⟩,
      (closedBall_subset_closedBall (min_le_left _ _)).trans (hsourceBuffer q hqS)⟩
  · have hscale : 0 < scale := hα.trans_le hs.1
    let v : Euclidean (d+1) × Euclidean (d+1) :=
      (q.1, scale • ComparisonChart.familyGradient charts η q.1)
    have hvP : v ∈ positiveConicLift (ComparisonChart.familyGradient charts)
        (ball 0 (2*r)) univ := ⟨hball n hn q hq, η, mem_univ _, scale, hscale, rfl⟩
    have hvE : v ∈ protectedAnnularCarrier (cthickening 1 B) a b (min εS ε) Γ := by
      refine ⟨⟨hbaseq n hn q hq, ?_⟩,
        (closedBall_subset_closedBall (min_le_right _ _)).trans (hbuffer v hvP)⟩
      change a ≤ ‖scale • ComparisonChart.familyGradient charts η q.1‖ ∧
        ‖scale • ComparisonChart.familyGradient charts η q.1‖ ≤ b
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      obtain ⟨hlo, hup⟩ := hnorm η q.1 (ball_subset_closedBall (hball n hn q hq))
      exact ⟨haG.le.trans (mul_le_mul hs.1 hlo hc.le hscale.le),
        (mul_le_mul hs.2 hup (norm_nonneg _) hβ.le).trans hbG.le⟩
    have hdist : dist q v = ‖q.2 - scale • ComparisonChart.familyGradient charts η q.1‖ := by
      change max (dist q.1 q.1)
        (dist q.2 (scale • ComparisonChart.familyGradient charts η q.1)) = _
      rw [dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    have hclose : dist q v ≤ δfinal := hdist ▸ he.trans ((mul_le_mul_of_nonneg_right
      (bufferedGraphError_mono hL (by positivity) hn) ht).trans htA)
    exact hplateau (mem_cthickening_of_dist_le _ _ _ _ hvE hclose)

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
