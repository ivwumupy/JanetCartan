module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.UniformTransport
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.RelationGeometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.SourceNeighborhood

/-!
# A terminal carrier before the final mask is selected

The source annulus and the comparison-gradient bounds fix one terminal annulus
before the selected root family. The literal reflected transport estimate then
preserves the same scaled comparison graph at every non-diagonal step. Diagonal
and depth-zero branches retain the original source. This exposes the geometric
input of `SignedProductEstimates.exists_common_normalizedSource_terminal_localizer`
without selecting another final mask.

The primitive producers are the retained comparison cover and gradient bounds in
`ProtectedFlow.exists_initialized_signed_no_return_with_graph_bounds`, and the
selected root/flow bounds used by `SelectedEvenProofMasks.SelectedApplication`.
Their application on the original initialized family is a separate obligation.
Sources: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection

open ProtectedMasks SelectedEvenProofMasks RegularSector.Characteristic
open ActualCarriers HamiltonPhase ProtectedFlow PhaseCover FiniteChain.Graph

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => E × E

/-- The retained compact source has a positive angular margin before any
current coefficients or word depth. This supplies the unchanged-source branch
of terminal protection (`app:ch_regular:thm:no-return`). -/
theorem exists_compact_source_angular_margin {S : Set P} (hS : IsCompact S)
    {Γ : Set E} (hsource : S ⊆ physicalProtectedRegion Γ) :
    ∃ ε > (0 : ℝ), ∀ p ∈ S, closedBall (normalizedCovector p.2) ε ⊆ Γ := by
  have hn : ContinuousOn (fun p : P ↦ normalizedCovector p.2) S :=
    (continuous_snd.norm.continuousOn.inv₀
      (fun p hp ↦ norm_ne_zero_iff.mpr (hsource hp).1)).smul continuous_snd.continuousOn
  obtain ⟨ε, hε, hbuffer⟩ := (hS.image_of_continuousOn hn).exists_cthickening_subset_open
    isOpen_interior (by rintro _ ⟨p, hp, rfl⟩; exact (hsource hp).2)
  have himage (p : P) (hp : p ∈ S) : normalizedCovector p.2 ∈
      (fun p : P ↦ normalizedCovector p.2) '' S := ⟨p, hp, rfl⟩
  exact ⟨ε, hε, fun p hp ↦
    (closedBall_subset_cthickening (himage p hp) ε).trans
      (hbuffer.trans interior_subset)⟩

private theorem chain_source_or_scaled_graph {I : Type*}
    {R : P → P → Prop} {S : Set P} (g : I → E → E) {α β L : ℝ}
    (hstart : ∀ p ∈ S, ∀ q, R p q →
      ∃ η scale, scale ∈ Icc α β ∧ p.2 = scale • g η p.1)
    (htransport : ∀ η scale, scale ∈ Icc α β → ∀ p q, R p q →
      ‖q.2 - scale • g η q.1‖ ≤ L * ‖p.2 - scale • g η p.1‖)
    {p q : P} {n : ℕ} (hchain : PositiveConicChain R p q n) (hp : p ∈ S) :
    q ∈ S ∨ ∃ η scale, scale ∈ Icc α β ∧ q.2 = scale • g η q.1 := by
  have step {p q : P} (hpq : R p q) {η : I} {scale : ℝ}
      (hs : scale ∈ Icc α β) (he : p.2 = scale • g η p.1) :
      q.2 = scale • g η q.1 := by
    have hb := htransport η scale hs p q hpq
    rw [he, sub_self, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  have propagate {p q : P} {n : ℕ} (hc : PositiveConicChain R p q n)
      (hp : p ∈ S ∨ ∃ η scale, scale ∈ Icc α β ∧ p.2 = scale • g η p.1) :
      q ∈ S ∨ ∃ η scale, scale ∈ Icc α β ∧ q.2 = scale • g η q.1 := by
    induction hc with
    | refl p => exact hp
    | tail hstep _ ih =>
      apply ih
      rcases hstep with rfl | hstep
      · exact hp
      · right
        rcases hp with hp | ⟨η, scale, hs, he⟩
        · obtain ⟨η, scale, hs, he⟩ := hstart _ hp _ hstep
          exact ⟨η, scale, hs, step hstep hs he⟩
        · exact ⟨η, scale, hs, step hstep hs he⟩
  exact propagate hchain (Or.inl hp)

/-- One protected annular carrier contains every finite mixture of the
literal selected relation, its covector reflection and diagonal steps. Its
annulus and angular width precede the root family, current coefficients,
elapsed interval and word depth. Only primitive section, speed, flow and
comparison-chart bounds occur as inputs; there is no assumed reachable-set
protection or all-chain angular premise. The source branch is protected by
its retained compact angular margin (`app:ch_regular:thm:no-return`,
`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_reflected_terminal_carrier
    {S : Set P} (hS : IsCompact S) {B Ω Γ : Set E} {r c C ε : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ Ω)
    (hΩΓ : Ω ⊆ interior Γ) :
    ∃ a > (0 : ℝ), ∃ b > a, ∃ εterminal > (0 : ℝ),
    ∀ {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
      (η₀ : J → Euclidean d) (εroot G : J → ℝ), (∀ j, 0 ≤ G j) →
    ∀ {M Lx κ Δ : ℝ}, 0 ≤ M → 0 ≤ Lx → 0 < κ → 0 ≤ Δ →
    ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (hQ : ContDiff ℝ ∞ Q),
      cNorm (closedBall 0 (2*r)) 3 Q ≤ M →
    ∀ (i : J → Fin (d+1)) (h : J → RootState (Euclidean d) → ℝ)
      (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (U K D : J → Set (RootState (Euclidean d))) (W : Set E)
      (χsource χout : J → E → ℂ),
      (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
      (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
        determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
          ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
        fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
          ((coordinateSplit (i j)).symm (h j v, v.2.2))
          ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
      (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2*r) →
      (∀ j v, v ∈ K j → v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
        (1/2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
      (∀ j v, v ∈ U j ∪ K j →
        (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
      (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
    ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
      (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
        (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
      (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
    ∀ (I : Type*) (g : I → ComparisonGeometry E)
      (charts : (j : I) → ComparisonChart
        (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
      (∀ j, r ≤ (g j).radius) →
      (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2*r),
        ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
      (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2*r),
        c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
          ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
      (∀ p ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q p = 0 →
        p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2*r)) univ) →
      (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2*r)) univ,
        closedBall (normalizedCovector p.2) ε ⊆ Γ) →
      ∀ n, reachableAt (reflectedProofRelation
        (physicalDirectRelation i h Φ U K W χsource χout Δ)) S n ⊆
          protectedAnnularCarrier B a b εterminal Γ := by
  obtain ⟨aS, haS, hlow⟩ := CompatibleResponse.exists_uniform_positive_bound hS
    continuous_snd.norm.continuousOn (fun p hp ↦ norm_pos_iff.mpr (hsource p hp).2.1)
  obtain ⟨bS, hhigh⟩ := hS.exists_bound_of_continuousOn continuous_snd.continuousOn
  obtain ⟨εS, hεS, hsourceBuffer⟩ := exists_compact_source_angular_margin hS
    (fun p hp ↦ ⟨(hsource p hp).2.1, hΩΓ (hsource p hp).2.2⟩)
  let α := aS / C
  let β := max α (bS / c)
  have hα : 0 < α := div_pos haS hC
  have hαβ : α ≤ β := le_max_left _ _
  have hβ : 0 < β := hα.trans_le hαβ
  let a := min aS (α*c)
  let b := max a (max bS (β*C)) + 1
  refine ⟨a, lt_min haS (mul_pos hα hc), b,
    (le_max_left _ _).trans_lt (lt_add_one _), min εS ε, lt_min hεS hε, ?_⟩
  intro J _ ℓ η₀ εroot G hG M Lx κ Δ hM hLx hκ hΔ Q hQ hQM
    i h Φ U K D W χsource χout hD hh hroot hKD hW hprimitive hbase hgap
    z Rflow rFlow T hflow htime hUflow I g charts hgr hderiv hnorm hcover hbuffer
  obtain ⟨L, _, htransport⟩ := exists_uniform_reflectedProofRelation_comparison_transport
    ℓ η₀ εroot G hG (show 0 < 2*r by positivity) hM hc hC hLx hκ hΔ hα hαβ
  let R := reflectedProofRelation (physicalDirectRelation i h Φ U K W χsource χout Δ)
  have hstep (η : ComparisonGeometry.ParameterFamily g) :=
    (htransport Q hQ hQM i h Φ U K D W χsource χout hD hh hroot hKD hW
      hprimitive hgap z Rflow rFlow T hflow htime hUflow (g η.1) (charts η.1)
      (by linarith [hgr η.1]) (hderiv η.1)
      (fun ξ hξ x hx ↦ hnorm ⟨η.1, ξ, hξ⟩ x hx) η.2.1 η.2.2).2
  have hstart : ∀ p ∈ S, ∀ q, R p q →
      ∃ η scale, scale ∈ Icc α β ∧ p.2 = scale • ComparisonChart.familyGradient charts η p.1 := by
    intro p hp q hpq
    have henergy : normalizedSymbol Q p = 0 :=
      reflectedProofRelation_source_energy hKD
        (fun j v hv ↦ (hflow j).initial v (hUflow j hv))
        (fun j v hv t ht ↦ (hflow j).hasDerivAt (hUflow j hv)
          ⟨by linarith [ht.1, htime j], ht.2.trans_lt (htime j)⟩)
        (fun j v hv ↦ (hroot j v hv).2.1) hpq
    obtain ⟨η, scale, hs, he⟩ := comparison_source_scaled_cover hQ charts hc hC hcover
      (fun η x hx ↦ hnorm η x (ball_subset_closedBall
        (ball_subset_ball (by linarith) hx)))
      (hsource p hp).1 (hsource p hp).2.1 (hsource p hp).2.2
      (hlow p hp) (hhigh p hp) henergy
    exact ⟨η, scale, ⟨hs.1, hs.2.trans (le_max_right _ _)⟩, he⟩
  intro n q hq
  obtain ⟨p, hp, hchain⟩ := hq
  have hbaseq : q.1 ∈ B := by
    have hb := hSB p hp
    clear hp
    induction hchain with
    | refl p => exact hb
    | tail hstep _ ih =>
      apply ih
      rcases hstep with rfl | hstep
      · exact hb
      · exact (reflectedProofRelation_base_mem_of_root_buffer hbase hstep).2
  rcases chain_source_or_scaled_graph (ComparisonChart.familyGradient charts) hstart
      hstep hchain hp with hqS | ⟨η, scale, hs, he⟩
  · exact ⟨⟨hbaseq, (min_le_left _ _).trans (hlow q hqS),
      (hhigh q hqS).trans ((le_max_left _ _).trans
        ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)))⟩,
      (closedBall_subset_closedBall (min_le_left _ _)).trans (hsourceBuffer q hqS)⟩
  · have hspos : 0 < scale := hα.trans_le hs.1
    have hqP : q ∈ positiveConicLift (ComparisonChart.familyGradient charts)
        (ball 0 (2*r)) univ := ⟨hBball hbaseq, η, mem_univ _, scale, hspos, he⟩
    refine ⟨⟨hbaseq, ?_⟩,
      (closedBall_subset_closedBall (min_le_right _ _)).trans (hbuffer q hqP)⟩
    change a ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ b
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    obtain ⟨hlo, hup⟩ := hnorm η q.1 (ball_subset_closedBall (hBball hbaseq))
    exact ⟨(min_le_right _ _).trans (mul_le_mul hs.1 hlo hc.le hspos.le),
      (mul_le_mul hs.2 hup (norm_nonneg _) hβ.le).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans
          (le_add_of_nonneg_right zero_le_one)))⟩

end JanetCartan.ArbitraryAccuracy.NormalizedTerminalProtection
