module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameFamily
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.Restriction

/-!
# Quantitative charts with the identified frozen reference

The output below is constructed from primitive frame data. It retains one
family before every derivative order and tolerance, and compares it to the
actual frozen reference, identified by root/ODE/inverse uniqueness in
`FrameFamily`. The consumer is the final decorated patch construction in
`app:ch_seed:prop:seed-actual-menu`, Step 1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- Output of `exists_localQuantitativeFamily`, before the final patch
shrinking. Every analytic field is proved by that constructor from the literal
normalized determinant (`app:lem:common-hamilton-phase`). -/
structure LocalQuantitativeFamily {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ}
    (N : LocalFrozenReference a) (U : Set (Euclidean n)) (hU : IsOpen U) where
  threshold : ℝ
  threshold_pos : 0 < threshold
  radius : ℝ
  radius_pos : 0 < radius
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  coefficient : ℕ → ℝ
  coefficient_pos : ∀ m, 0 < coefficient m
  reference_target : ball (a.embedding a.baseData.1, a.baseData.2) (2 * radius) ⊆
    N.family.chart.target
  flow : (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < threshold}) →
    HamiltonFlow (normalizedHomogeneousSymbol hU Q.1 Q.2.1) (Euclidean (n - 1))
  chart : (Q : _) → ProjectionChart (flow Q)
  section_eq : ∀ Q, (flow Q).sectionMap = a.embedding.toContinuousLinearMap
  target_contains : ∀ Q, ball (a.embedding a.baseData.1, a.baseData.2) (2 * radius) ⊆
    (chart Q).target
  source_eq : ∀ Q, (chart Q).source = ball ((0 : ℝ), a.baseData) (3 * sourceRadius) ∩
    (flow Q).augmentedProjection ⁻¹' (chart Q).target
  source_admissible : ∀ Q, ball ((0 : ℝ), a.baseData) (3 * sourceRadius) ⊆
    (flow Q).time ×ˢ (flow Q).parameters
  state_mem : ∀ Q, ∀ q ∈ (flow Q).time ×ˢ (flow Q).parameters,
    ((flow Q).position q, (flow Q).momentum q) ∈ closedBall (0, ξ) N.stateRadius
  momentum_smooth : ∀ Q, ContDiffOn ℝ ∞ (flow Q).momentum ((flow Q).time ×ˢ (flow Q).parameters)
  coordinates_smooth : ∀ Q, ContDiffOn ℝ ∞ (chart Q).coordinates
    (ball (a.embedding a.baseData.1, a.baseData.2) (2 * radius))
  phase_smooth : ∀ Q, ContDiffOn ℝ ∞ (phase (chart Q).coordinates)
    (ball (a.embedding a.baseData.1, a.baseData.2) (2 * radius))
  phase_bound : ∀ Q m, cNorm (closedBall (a.embedding a.baseData.1, a.baseData.2) radius) m
    (phase (chart Q).coordinates) ≤ coefficient m *
      (1 + cNorm (closedBall (0 : Euclidean n) N.stateRadius) (m + 1) Q.1)
  phase_continuity : ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ Q,
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) (m + 1)
      (Q.1 - fun _ ↦ cubeStress n) < d →
    cNorm (closedBall (a.embedding a.baseData.1, a.baseData.2) radius) m
      (phase (chart Q).coordinates - phase N.family.chart.coordinates) < ε

set_option maxHeartbeats 1600000 in
/-- Construct the quantitative family against the actual frozen chart.
The whole-ball transverse premise is produced by
`exists_transverse_localFrozenReference_in_physical_ball`; no phase or momentum
comparison is assumed (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_localQuantitativeFamily {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    (N : LocalFrozenReference a)
    (hgapN : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ ≠ 0)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    Nonempty (LocalQuantitativeFamily N U hU) := by
  obtain ⟨δ, r, ρ, R', κ, B, A, Φ₀, C₀, hδ, hr, hρ, _hR', hRR, hB, _hC₀t,
    hS₀, hκ, hκρ, hκtarget, hbenchmark, F, C, hprops, hcont, _hcomp⟩ :=
    exists_current_frame_phase_family hξ hchar a N hgapN hU hdomain
  let y₀ := (a.embedding a.baseData.1, a.baseData.2)
  have hκρ' : κ ≤ ρ := by linarith
  have hsub : ball y₀ (2 * κ) ⊆ ball y₀ (2 * ρ) :=
    ball_subset_ball (by linarith)
  refine ⟨{
    threshold := δ
    threshold_pos := hδ
    radius := κ
    radius_pos := hκ
    sourceRadius := r
    sourceRadius_pos := hr
    coefficient := B
    coefficient_pos := hB
    reference_target := hκtarget
    flow := F
    chart := C
    section_eq := fun Q ↦ (hprops Q).1
    target_contains := fun Q ↦ hsub.trans (hprops Q).2.1
    source_eq := fun Q ↦ (hprops Q).2.2.1
    source_admissible := fun Q ↦ (hprops Q).2.2.2.2.1
    state_mem := ?_
    momentum_smooth := ?_
    coordinates_smooth := ?_
    phase_smooth := ?_
    phase_bound := ?_
    phase_continuity := ?_ }⟩
  · intro Q q hq
    exact closedBall_subset_closedBall hRR.le ((hprops Q).2.2.2.2.2.2.1 q hq)
  · intro Q
    exact (hprops Q).2.2.2.2.2.2.2.2.2.1
  · intro Q
    exact ((hprops Q).2.2.2.2.2.2.2.2.2.2.1).mono hsub
  · intro Q
    exact ((hprops Q).2.2.2.2.2.2.2.2.2.2.2.1).mono hsub
  · intro Q m
    obtain ⟨_hj, _ht, _hs, _hb, _ha, _hh, _hr, _hg, _hx, _hp, _hC, hS, hbound⟩ := hprops Q
    have hmono := cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hκρ')
      (isCompact_closedBall y₀ ρ)
      (fun z hz ↦ (hS.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith : ρ < 2 * ρ) hz))).of_le
          (by simp : (m : ℕ∞ω) ≤ ∞))
    exact hmono.trans ((le_add_of_nonneg_left
      (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _))).trans (hbound m))
  · intro m ε hε
    obtain ⟨d, hd, hc⟩ := hcont m ε hε
    refine ⟨d, hd, fun Q hq ↦ ?_⟩
    rw [← cNorm_sub_eq_of_phase_eqOn isOpen_ball
      (closedBall_subset_ball (by linarith : κ < 2 * κ)) hbenchmark]
    have hS := (hprops Q).2.2.2.2.2.2.2.2.2.2.2.1
    have hmono := cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hκρ')
      (isCompact_closedBall y₀ ρ)
      (fun z hz ↦ ((hS.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith : ρ < 2 * ρ) hz))).sub
          (hS₀.contDiffAt (isOpen_ball.mem_nhds
            (closedBall_subset_ball (by linarith : ρ < 2 * ρ) hz)))).of_le
              (by simp : (m : ℕ∞ω) ≤ ∞))
    exact hmono.trans_lt (hc Q hq)

/-- Each requested positive full momentum/Fréchet comparison tolerance has a
positive primitive frame threshold. The fixed family and low neighborhood
remain unchanged (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem LocalQuantitativeFamily.exists_momentum_comparison_threshold
    {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ} {N : LocalFrozenReference a}
    {U : Set (Euclidean n)} {hU : IsOpen U} (L : LocalQuantitativeFamily N U hU)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < d →
      ∀ q ∈ closedBall (a.embedding a.baseData.1, a.baseData.2) L.radius,
        ‖(L.chart Q).chartMomentum q - N.family.chart.chartMomentum q‖ < ε ∧
        ‖fderiv ℝ (L.chart Q).chartMomentum q -
          fderiv ℝ N.family.chart.chartMomentum q‖ < ε := by
  obtain ⟨d, hd, hc⟩ := L.phase_continuity 2 ε hε
  refine ⟨d, hd, fun Q hq q hqK ↦ ?_⟩
  have hcomp := hc Q ((cNorm_mono_order (by omega : 2 + 1 ≤ 6)).trans_lt hq)
  have hKW : closedBall (a.embedding a.baseData.1, a.baseData.2) L.radius ⊆
      ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius) :=
    closedBall_subset_ball (by linarith [L.radius_pos])
  have hR : ContDiffOn ℝ ∞ N.family.chart.coordinates N.family.chart.target := by
    rw [N.family.reference_control.target_eq]
    exact N.family.reference_control.coordinates_smooth
  have hS : ContDiffOn ℝ ∞ (phase N.family.chart.coordinates) N.family.chart.target :=
    N.family.chart.contDiffOn_phase hR
  have hb := chartMomentum_comparison_le_phase_cNorm_two (L.chart Q) N.family.chart
    (isCompact_closedBall _ _) (hKW.trans (L.target_contains Q)) (hKW.trans L.reference_target)
    (fun z hz ↦ (L.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds (hKW hz)))
    (fun z hz ↦ hS.contDiffAt (N.family.chart.isOpen_target.mem_nhds
      (L.reference_target (hKW hz)))) hqK
  exact ⟨hb.1.trans_lt hcomp, hb.2.trans_lt hcomp⟩

end JanetCartan.ActualCarriers.CurrentFullPhase
