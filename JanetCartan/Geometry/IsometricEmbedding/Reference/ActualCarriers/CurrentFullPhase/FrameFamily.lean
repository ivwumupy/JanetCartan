module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentCharts
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.MomentumComparison
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameContinuousFamily

/-!
# One quantitative Hamilton family from primitive frame closeness

Instantiate `app:lem:common-hamilton-phase` with the literal normalized
determinant. One fixed componentwise frame `C⁶` neighborhood supplies the
actual charts, all-order one-high estimates at frame order `m + 1`, and
finite-order continuity from frame order `m + 1` to phase order `m`.

The full momentum and its full Fréchet derivative are compared on a fixed
closed target ball. Zero-error continuity identifies the benchmark with the
family's frozen member; root/ODE/inverse uniqueness then identifies its phase
with the actual frozen reference on a smaller open target. `LocalFamily` and
`PatchFamily` retain that target before the final decorated patch shrinking
and construct the `CarrierFullPhaseInput` objects.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

set_option maxHeartbeats 1600000 in
/-- Actual normalized-determinant charts, sharp bounds, and finite-order
continuity from primitive frame data (`app:ch_seed:prop:seed-actual-menu`, Step 1;
`app:ch_seed:eq:seed-phase-tame`). The charts precede all orders and tolerances.
The case `m = 5` uses exactly frame `C⁶` comparison, while the high estimate
uses frame order `m + 1`, hence immersion order `m + 3` under the independently
proved loss-two projected-frame estimate. No symbol, phase, momentum, or
flow estimate is an input. -/
theorem exists_current_frame_phase_family {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    (N : LocalFrozenReference a)
    (hgapN : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ ≠ 0)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    let y₀ := (a.embedding a.baseData.1, a.baseData.2)
    ∃ (δ r ρ R' κ : ℝ) (B : ℕ → ℝ)
      (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
        (Euclidean n × (ℝ × Euclidean (n - 1))))
      (Φ₀ : HamiltonFlow (frozenSymbol n) (Euclidean (n - 1))) (C₀ : ProjectionChart Φ₀),
      0 < δ ∧ 0 < r ∧ 0 < ρ ∧ 0 < R' ∧ R' < N.stateRadius ∧ (∀ m, 0 < B m) ∧
      ball y₀ (2 * ρ) ⊆ C₀.target ∧
      ContDiffOn ℝ ∞ (phase C₀.coordinates) (ball y₀ (2 * ρ)) ∧
      0 < κ ∧ 2 * κ < ρ ∧ ball y₀ (2 * κ) ⊆ N.family.chart.target ∧
      EqOn (phase C₀.coordinates) (phase N.family.chart.coordinates) (ball y₀ (2 * κ)) ∧
      let S := {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < δ}
      ∃ (F : (Q : S) → HamiltonFlow (normalizedHomogeneousSymbol hU Q.1 Q.2.1)
          (Euclidean (n - 1))) (C : (Q : S) → ProjectionChart (F Q)),
        (∀ Q,
          (F Q).sectionMap = a.embedding.toContinuousLinearMap ∧
          ball y₀ (2 * ρ) ⊆ (C Q).target ∧
          (C Q).source = ball ((0 : ℝ), a.baseData) (3 * r) ∩
            (F Q).augmentedProjection ⁻¹' (C Q).target ∧
          (C Q).source ⊆ ball ((0 : ℝ), a.baseData) (2 * r) ∧
          ball ((0 : ℝ), a.baseData) (3 * r) ⊆ (F Q).time ×ˢ (F Q).parameters ∧
          (∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * r),
            ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (F Q).augmentedProjection q) -
              ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
          (∀ q ∈ (F Q).time ×ˢ (F Q).parameters,
            ((F Q).position q, (F Q).momentum q) ∈ closedBall (0, ξ) R') ∧
          (∀ z ∈ closedBall (0, ξ) R',
            ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, a.normal⟫_ℝ ≠ 0) ∧
          ContDiffOn ℝ ∞ (F Q).position ((F Q).time ×ˢ (F Q).parameters) ∧
          ContDiffOn ℝ ∞ (F Q).momentum ((F Q).time ×ˢ (F Q).parameters) ∧
          ContDiffOn ℝ ∞ (C Q).coordinates (ball y₀ (2 * ρ)) ∧
          ContDiffOn ℝ ∞ (phase (C Q).coordinates) (ball y₀ (2 * ρ)) ∧
          (∀ m, cNorm (closedBall a.baseData r ×ˢ Icc (-r) r) m
              (fun q ↦ ((F Q).position (q.2, q.1), (F Q).momentum (q.2, q.1))) +
            cNorm (closedBall y₀ ρ) m (C Q).coordinates +
            cNorm (closedBall y₀ ρ) m (phase (C Q).coordinates) ≤
              B m * (1 + cNorm (closedBall (0 : Euclidean n) N.stateRadius) (m + 1) Q.1))) ∧
        (∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ Q,
          cNorm (closedBall (0 : Euclidean n) N.stateRadius) (m + 1)
            (Q.1 - fun _ ↦ cubeStress n) < d →
            cNorm (closedBall y₀ ρ) m
              (phase (C Q).coordinates - phase C₀.coordinates) < ε) ∧
        (∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ Q,
          cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
            (Q.1 - fun _ ↦ cubeStress n) < d →
          ∀ q ∈ closedBall y₀ ρ,
            ‖(C Q).chartMomentum q - C₀.chartMomentum q‖ < ε ∧
            ‖fderiv ℝ (C Q).chartMomentum q - fderiv ℝ C₀.chartMomentum q‖ < ε) := by
  let y₀ := (a.embedding a.baseData.1, a.baseData.2)
  have hball : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  have hphysical : closedBall (0 : Euclidean n) N.stateRadius ⊆ U := by
    intro x hx
    apply hdomain (x, ξ)
    apply hball
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hx
  have hzero (p) (hp : p ∈ closedBall ξ N.stateRadius) : p ≠ 0 := by
    apply (mem_frozenSymbol_domain (0, p)).mp
    apply N.state_subset
    apply hball
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hp
  have henergy : (frozenSymbol n).h
      (transverseSectionState a.embedding a.normal (a.baseData, ⟪a.normal, ξ⟫_ℝ)) =
        a.baseData.2.1 := by
    rw [a.baseState_eq, frozenSymbol_h]
    simp [hchar, AdaptedSection.baseData]
  have htrans : ⟪(frozenSymbol n).hp
      (transverseSectionState a.embedding a.normal (a.baseData, ⟪a.normal, ξ⟫_ℝ)), a.normal⟫_ℝ ≠ 0 := by
    rw [a.baseState_eq]
    exact (frozenSymbol_transverse_pos hξ hchar a.determinant_positive).ne'
  obtain ⟨r, ρ, δH, R', BH, A, Φ₀, C₀, hr, hρ, hδH, hR', hRR, hBH,
      hC₀t, hS₀, FH, CH, hprops, hcont⟩ :=
    exists_commonTameContinuousHamiltonPhases (frozenSymbol n) N.state_open N.state_subset
      ((frozenSymbol_smooth n).mono N.state_subset) a.embedding a.normal a.orthogonal a.spanning
      N.stateRadius_pos N.stateBall_subset henergy htrans
  let Hzero : {H : HomogeneousSymbol (Euclidean n) //
      N.stateDomain ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h N.stateDomain ∧
      cNorm (closedBall (transverseSectionState a.embedding a.normal
        (a.baseData, ⟪a.normal, ξ⟫_ℝ)) N.stateRadius) 3
        (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ δH} :=
    ⟨frozenSymbol n, N.state_subset, (frozenSymbol_smooth n).mono N.state_subset, by
      simp only [sub_self]
      exact (cNorm_zero _ _).le.trans hδH.le⟩
  obtain ⟨hjz, htz, _hsz, hbufz, hadmz, hhalfz, hrangez, _hgapz,
    _hxz, _hpz, _hCz, hSz, _hidz, _hboundz⟩ := hprops Hzero
  have hzeroPhase : EqOn (phase C₀.coordinates) (phase (CH Hzero).coordinates)
      (ball y₀ ρ) := by
    intro z hz
    have hzK := ball_subset_closedBall hz
    have hnorm : ‖phase (CH Hzero).coordinates z - phase C₀.coordinates z‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨d, hd, hc⟩ := hcont 0 ε hε
      have hsmall : cNorm (closedBall (transverseSectionState a.embedding a.normal
          (a.baseData, ⟪a.normal, ξ⟫_ℝ)) N.stateRadius) (0 + 1)
          (fun z ↦ Hzero.1.h z - (frozenSymbol n).h z) < d := by
        simp only [Hzero, sub_self]
        exact (cNorm_zero _ _).trans_lt hd
      have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
        (isCompact_closedBall y₀ ρ)
        (fun w hw ↦ ((hSz.contDiffAt (isOpen_ball.mem_nhds
            (closedBall_subset_ball (by linarith : ρ < 2 * ρ) hw))).sub
          (hS₀.contDiffAt (isOpen_ball.mem_nhds
            (closedBall_subset_ball (by linarith : ρ < 2 * ρ) hw)))).of_le
              (by simp : (0 : ℕ∞ω) ≤ ∞)) hzK (le_refl 0)
      simpa only [norm_iteratedFDeriv_zero, zero_add] using hb.trans (hc Hzero hsmall).le
    exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))).symm
  have hbase : y₀ ∈ N.family.chart.target := by
    rw [N.family.reference_control.target_eq]
    exact N.family.base_mem
  obtain ⟨e, he, heV⟩ := Metric.isOpen_iff.mp N.family.chart.isOpen_target _ hbase
  have hrN := N.family.sourceRadius_pos
  let η := min (3 * r) (3 * N.family.sourceRadius) /
    (2 * (‖(A.symm : (Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ]
      (ℝ × InitialData (Euclidean (n - 1))))‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let κ := min ρ (min e η) / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκρ : 2 * κ < ρ := by
    have hh := min_le_left ρ (min e η); dsimp [κ]; linarith
  have hκe : 2 * κ < e := by
    have hh := (min_le_right ρ (min e η)).trans (min_le_left e η)
    dsimp [κ]; linarith
  have hκη : 2 * κ < η := by
    have hh := (min_le_right ρ (min e η)).trans (min_le_right e η)
    dsimp [κ]; linarith
  have hκtarget : ball y₀ (2 * κ) ⊆ N.family.chart.target :=
    (ball_subset_ball hκe.le).trans heV
  have hν : a.normal ≠ 0 := by
    intro heq
    have hh := a.normal_unit
    rw [heq, norm_zero] at hh
    norm_num at hh
  have hcoords := (CH Hzero).coordinates_eq_on_transverse_overlap N.family.chart
    N.state_open N.state_subset ((frozenSymbol_smooth n).mono N.state_subset)
    hball a.embedding a.normal hν a.orthogonal a.spanning hjz
    N.family.reference_control.section_eq hgapN
    (by positivity : 0 < 3 * r)
    (by positivity : 0 < 3 * N.family.sourceRadius) A hadmz
    (fun _ hq ↦ N.family.reference_control.source_admissible (subset_closure hq))
    (hbufz.trans (ball_subset_ball (by linarith)))
    (by rw [N.family.reference_control.target_eq]; exact N.family.reference_control.source_eq)
    hhalfz
    (fun q hq ↦ closedBall_subset_closedBall hRR.le (by
      simpa only [a.baseState_eq] using hrangez q hq))
    (fun q hq ↦ by simpa only [a.baseState_eq] using N.family.reference_control.state_mem q hq)
  have hbenchmark : EqOn (phase C₀.coordinates) (phase N.family.chart.coordinates)
      (ball y₀ (2 * κ)) := by
    intro z hz
    rw [hzeroPhase (ball_subset_ball hκρ.le hz)]
    have heq := hcoords ⟨⟨htz (ball_subset_ball (by linarith) hz), hκtarget hz⟩,
      ball_subset_ball hκη.le hz⟩
    simp only [phase, heq]
  obtain ⟨δ₀, hδ₀, hsmall⟩ := NormalizedSymbolBounds.exists_cube_symbol_C3_C6_comparison_radius
    (0, ξ) N.stateRadius_pos hzero hδH zero_lt_one
  let δ := min 1 δ₀
  have hδ : 0 < δ := lt_min zero_lt_one hδ₀
  let S := {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < δ}
  let H (Q : S) : {H : HomogeneousSymbol (Euclidean n) //
      N.stateDomain ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h N.stateDomain ∧
      cNorm (closedBall (transverseSectionState a.embedding a.normal
        (a.baseData, ⟪a.normal, ξ⟫_ℝ)) N.stateRadius) 3
        (fun z ↦ H.h z - (frozenSymbol n).h z) ≤ δH} :=
    ⟨normalizedHomogeneousSymbol hU Q.1 Q.2.1,
      (fun q hq ↦ ⟨hdomain q hq, (mem_frozenSymbol_domain q).mp (N.state_subset hq)⟩),
      (contDiffOn_normalizedSymbol hU Q.2.1).mono
        (fun q hq ↦ ⟨hdomain q hq, (mem_frozenSymbol_domain q).mp (N.state_subset hq)⟩),
      (by
        rw [a.baseState_eq]
        exact (hsmall U hU hphysical Q.1 Q.2.1
          (Q.2.2.trans_le (min_le_right _ _))).1.le)⟩
  let F (Q : S) := FH (H Q)
  let C (Q : S) : ProjectionChart (F Q) := CH (H Q)
  have hQbound (Q : S) : ∀ x ∈ closedBall (0 : Euclidean n) N.stateRadius,
      ‖Q.1 x‖ ≤ ‖cubeStress n‖ + 1 := by
    intro x hx
    have hdiff : ∀ z ∈ closedBall (0 : Euclidean n) N.stateRadius,
        ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) z := fun z hz ↦
      ((Q.2.1.contDiffAt (hU.mem_nhds (hphysical hz))).sub contDiffAt_const).of_le (by simp)
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall _ _) hdiff hx (by omega : 0 ≤ 6)
    simp only [norm_iteratedFDeriv_zero, Pi.sub_apply] at hb
    have hs := Q.2.2.trans_le (min_le_left 1 δ₀)
    have ht := norm_add_le (Q.1 x - cubeStress n) (cubeStress n)
    rw [sub_add_cancel] at ht
    linarith
  choose D hD hDbound using fun m : ℕ ↦
    NormalizedSymbolBounds.exists_cNorm_symbol_le_frame_contDiffOn
      (0, ξ) N.stateRadius_pos hzero (‖cubeStress n‖ + 1) (m + 1)
  let B (m : ℕ) := BH m * (1 + D m)
  have hB (m : ℕ) : 0 < B m := mul_pos (hBH m) (by linarith [hD m])
  have hcontinuity : ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ Q : S,
      cNorm (closedBall (0 : Euclidean n) N.stateRadius) (m + 1)
        (Q.1 - fun _ ↦ cubeStress n) < d →
      cNorm (closedBall y₀ ρ) m (phase (C Q).coordinates - phase C₀.coordinates) < ε := by
    intro m ε hε
    obtain ⟨dH, hdH, hcH⟩ := hcont m ε hε
    obtain ⟨d, hd, hdframe⟩ := NormalizedSymbolBounds.exists_symbol_comparison_radius_contDiffOn
      (0, ξ) N.stateRadius_pos hzero (cubeStress n) (m + 1) hdH
    refine ⟨d, hd, ?_⟩
    intro Q hq
    apply hcH (H Q)
    change cNorm (closedBall (transverseSectionState a.embedding a.normal
      (a.baseData, ⟪a.normal, ξ⟫_ℝ)) N.stateRadius) (m + 1)
        (normalizedSymbol Q.1 - normalizedSymbol (fun _ ↦ cubeStress n)) < dH
    rw [a.baseState_eq]
    exact hdframe U hU hphysical Q.1 Q.2.1 hq
  refine ⟨δ, r, ρ, R', κ, B, A, Φ₀, C₀, hδ, hr, hρ, hR', hRR, hB, hC₀t, hS₀,
    hκ, hκρ, hκtarget, hbenchmark, F, C, ?_, hcontinuity, ?_⟩
  · intro Q
    obtain ⟨hj, ht, hs, hbuf, hadm, hhalf, hrange, hgap, hx, hp, hC, hS,
      _hid, hbound⟩ := hprops (H Q)
    simp only [a.baseState_eq] at hrange hgap hbound
    refine ⟨hj, ht, hs, hbuf, hadm, hhalf, hrange, hgap, hx, hp, hC, hS, ?_⟩
    intro m
    have hb := hDbound m U hU hphysical Q.1 Q.2.1 (hQbound Q)
    have hh := hbound m
    change _ ≤ BH m * (1 + cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
      (normalizedSymbol Q.1)) at hh
    apply hh.trans
    change _ ≤ BH m * (1 + D m) * _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hBH m).le
    nlinarith [cNorm_nonneg (closedBall (0 : Euclidean n) N.stateRadius) (m + 1) Q.1]
  · intro ε hε
    obtain ⟨d, hd, hcomp⟩ := hcontinuity 2 ε hε
    refine ⟨d, hd, ?_⟩
    intro Q hq q hqK
    have hs := hcomp Q ((cNorm_mono_order (by omega : 2 + 1 ≤ 6)).trans_lt hq)
    obtain ⟨_hj, ht, _hs, _hbuf, _hadm, _hhalf, _hrange, _hgap, _hx, _hp, _hC, hS,
      _hid, _hbound⟩ := hprops (H Q)
    have hKW : closedBall y₀ ρ ⊆ ball y₀ (2 * ρ) := closedBall_subset_ball (by linarith)
    have hb := chartMomentum_comparison_le_phase_cNorm_two (C Q) C₀
      (isCompact_closedBall _ _) (hKW.trans ht) (hKW.trans hC₀t)
      (fun z hz ↦ hS.contDiffAt (isOpen_ball.mem_nhds (hKW hz)))
      (fun z hz ↦ hS₀.contDiffAt (isOpen_ball.mem_nhds (hKW hz))) hqK
    exact ⟨hb.1.trans_lt hs, hb.2.trans_lt hs⟩

end JanetCartan.ActualCarriers.CurrentFullPhase
