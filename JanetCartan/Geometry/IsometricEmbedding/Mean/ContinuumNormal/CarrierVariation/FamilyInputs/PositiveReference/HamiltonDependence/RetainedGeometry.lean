module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.InverseComparison

/-!
# Retaining the actual Hamilton comparison geometry

Consumer: positive-reference comparison of the SAME charts in
`FamilyInputs.PositiveReference.HamiltonDependence`, for
`app:lem:common-hamilton-phase`, `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'.

The existing local-family constructor forgets the transverse state ball and
normalized inverse gap. This constructor retains those witnesses from
`exists_current_frame_phase_family`, together with that producer's exact
flow and chart. No output continuity at a positive reference is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open HamiltonPhase ActualCarriers ActualCarriers.CurrentFullPhase
open FrozenMenu FrozenPhaseReference

set_option maxHeartbeats 1600000 in
/-- Retain the primitive transverse and inverse geometry for the actual local
family (`app:lem:common-hamilton-phase`). All witnesses precede the varying
frame and derivative order. The `LocalQuantitativeFamily` is built with exactly
the flow and chart returned by `exists_current_frame_phase_family`; its
original bounds and frozen comparison are preserved. The consumer must still
subtract the root/ODE/inverse equations at its positive reference. -/
theorem exists_localQuantitativeFamily_with_transverse_control {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    (N : LocalFrozenReference a)
    (hgapN : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ ≠ 0)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    ∃ (L : LocalQuantitativeFamily N U hU) (R : ℝ)
      (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
        (Euclidean n × (ℝ × Euclidean (n - 1)))),
      0 < R ∧ R < N.stateRadius ∧ ∀ Q,
        (L.chart Q).source ⊆ ball ((0 : ℝ), a.baseData) (2 * L.sourceRadius) ∧
        (∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
          ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
            ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
        (∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
          ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R) ∧
        (∀ z ∈ closedBall (0, ξ) R,
          ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, a.normal⟫_ℝ ≠ 0) ∧
        ContDiffOn ℝ ∞ (L.flow Q).position ((L.flow Q).time ×ˢ (L.flow Q).parameters) := by
  obtain ⟨δ, r, ρ, R', κ, B, A, Φ₀, C₀, hδ, hr, hρ, hR', hRR, hB, _hC₀t,
    hS₀, hκ, hκρ, hκtarget, hbenchmark, F, C, hprops, hcont, _hcomp⟩ :=
    exists_current_frame_phase_family hξ hchar a N hgapN hU hdomain
  let y₀ := (a.embedding a.baseData.1, a.baseData.2)
  have hκρ' : κ ≤ ρ := by linarith
  have hsub : ball y₀ (2 * κ) ⊆ ball y₀ (2 * ρ) :=
    ball_subset_ball (by linarith)
  have hgeometry (Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < δ}) :
      (C Q).source ⊆ ball ((0 : ℝ), a.baseData) (2 * r) ∧
      (∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * r),
        ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (F Q).augmentedProjection q) -
          ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
      (∀ q ∈ (F Q).time ×ˢ (F Q).parameters,
        ((F Q).position q, (F Q).momentum q) ∈ closedBall (0, ξ) R') ∧
      (∀ z ∈ closedBall (0, ξ) R',
        ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, a.normal⟫_ℝ ≠ 0) ∧
      ContDiffOn ℝ ∞ (F Q).position ((F Q).time ×ˢ (F Q).parameters) := by
    obtain ⟨_hj, _ht, _hs, hbuffer, _hadm, hhalf, hrange, hgap,
      hx, _hp, _hC, _hS, _hb⟩ := hprops Q
    exact ⟨hbuffer, hhalf, hrange, hgap, hx⟩
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
    phase_continuity := ?_ }, R', A, hR', hRR, hgeometry⟩
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


/-- The actual frame producer discharges every source-buffer, inverse-gap
and smoothness premise of the inverse comparison, retaining the same local
family and the transverse witnesses. Thus only the forward Hamilton projection
comparison remains before applying this implication at a positive reference.
This is checked progress toward `app:ch_background:prop:bg-frame`, not the
unconditional immersion-to-carrier continuity theorem. -/
theorem exists_localQuantitativeFamily_with_inverse_comparison {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0) (a : AdaptedSection ξ)
    (N : LocalFrozenReference a)
    (hgapN : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ ≠ 0)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    ∃ (L : LocalQuantitativeFamily N U hU) (R : ℝ)
      (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
        (Euclidean n × (ℝ × Euclidean (n - 1)))),
      0 < R ∧ R < N.stateRadius ∧ (∀ Q,
        (L.chart Q).source ⊆ ball ((0 : ℝ), a.baseData) (2 * L.sourceRadius) ∧
        (∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
          ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
            ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
        (∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
          ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R) ∧
        (∀ z ∈ closedBall (0, ξ) R,
          ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, a.normal⟫_ℝ ≠ 0) ∧
        ContDiffOn ℝ ∞ (L.flow Q).position ((L.flow Q).time ×ˢ (L.flow Q).parameters) ) ∧
      (∀ Q₀, ∀ K : Set (Euclidean n × (ℝ × Euclidean (n - 1))),
        IsCompact K →
        K ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius) →
        ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ Q,
          cNorm (closedBall ((0 : ℝ), a.baseData) (2 * L.sourceRadius)) m
            ((L.flow Q).augmentedProjection - (L.flow Q₀).augmentedProjection) < d →
          cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
            cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε) := by
  obtain ⟨L, R, A, hR, hRN, hgeometry⟩ :=
    exists_localQuantitativeFamily_with_transverse_control hξ hchar a N hgapN hU hdomain
  refine ⟨L, R, A, hR, hRN, hgeometry, ?_⟩
  intro Q₀ K hK hKV m ε hε
  exact exists_retained_coordinates_phase_sub_tolerance L A
    (fun Q ↦ (hgeometry Q).1) (fun Q ↦ (hgeometry Q).2.1)
    (fun Q ↦ (hgeometry Q).2.2.2.2) Q₀ hK hKV m hε

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
