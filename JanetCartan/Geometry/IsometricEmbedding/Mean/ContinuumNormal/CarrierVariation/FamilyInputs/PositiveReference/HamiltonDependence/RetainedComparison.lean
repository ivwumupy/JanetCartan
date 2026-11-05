module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.TransverseBuffer

/-!
# Comparing the same retained charts at a positive reference

For `app:lem:common-hamilton-phase` and `app:ch_osc:prop:osc-normal`, Step 4',
construct a comparison family about the actual initial momentum of a fixed
member. Root and ODE uniqueness identify its charts with the retained charts
on a genuine common open target. The differentiated root/ODE/inverse estimates
then compare those same retained coordinates and phases. The actual frame
producer discharges the geometric hypotheses in the final theorem below.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

set_option maxHeartbeats 1800000 in
/-- Finite-order comparison at any fixed admissible frame, using the SAME
retained inverse coordinates and phase. The source gap and transverse range
are geometric witnesses of `exists_current_frame_phase_family`, retained by
`exists_localQuantitativeFamily_with_transverse_control`; no output continuity
is a premise. The smaller open target precedes all orders, tolerances and
varying frames (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_positiveReference_comparison {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} {N : LocalFrozenReference a}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U)
    (L : LocalQuantitativeFamily N U hU) {R : ℝ} (hR : 0 < R)
    (hRN : R < N.stateRadius)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))))
    (hhalf : ∀ Q, ∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    (hrange : ∀ Q, ∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
      ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R)
    (Q₀ : _)
    (hgap₀ : ∀ z ∈ closedBall (0, ξ) R,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0) :
    ∃ ρ > (0 : ℝ), 2 * ρ < L.radius ∧
      ∀ K : Set (Euclidean n × (ℝ × Euclidean (n - 1))),
        IsCompact K → K ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * ρ) →
        ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
          cNorm (closedBall (0, ξ) N.stateRadius) (max 3 (m + 1))
            (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
          cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
            cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε := by
  let H (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold}) :=
    normalizedHomogeneousSymbol hU Q.1 Q.2.1
  have hND : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  have hDH (Q : _) : N.stateDomain ⊆ (H Q).domain := fun z hz ↦
    ⟨hdomain z hz, (mem_frozenSymbol_domain z).mp (N.state_subset hz)⟩
  have hH (Q : _) : ContDiffOn ℝ ∞ (H Q).h N.stateDomain :=
    (contDiffOn_normalizedSymbol hU Q.2.1).mono (hDH Q)
  have hν : a.normal ≠ 0 := by
    intro he
    have hh := a.normal_unit
    rw [he, norm_zero] at hh
    norm_num at hh
  have hsr := L.sourceRadius_pos
  have hLr := L.radius_pos
  have hbase := L.source_admissible Q₀
    (mem_ball_self (by positivity : 0 < 3 * L.sourceRadius))
  let p₀ := (L.flow Q₀).momentum (0, a.baseData)
  let τ₀ := ⟪a.normal, p₀⟫_ℝ / ⟪a.normal, a.normal⟫_ℝ
  let z₀ := transverseSectionState a.embedding a.normal (a.baseData, τ₀)
  have hp₀ : p₀ = τ₀ • a.normal + a.embedding a.baseData.2.2 :=
    sectionMomentum_eq_normal_add_tangent a.embedding a.normal p₀ hν a.orthogonal
      a.spanning a.baseData.2.2 (by
        simpa only [L.section_eq, LinearIsometry.coe_toContinuousLinearMap] using
          (L.flow Q₀).initial_momentum a.baseData hbase.2)
  have hz₀ : z₀ = ((L.flow Q₀).position (0, a.baseData), p₀) := by
    rw [(L.flow Q₀).initial_position a.baseData hbase.2, L.section_eq]
    exact Prod.ext rfl hp₀.symm
  have hzR : z₀ ∈ closedBall (0, ξ) R := by
    rw [hz₀]; exact hrange Q₀ _ hbase
  have henergy : (H Q₀).h z₀ = a.baseData.2.1 := by
    rw [hz₀]
    exact (L.flow Q₀).initial_energy _ hbase.2
  obtain ⟨S, δg, hRS, hSN, hδg, hgap⟩ := exists_positiveReference_transverse_buffer
    (H Q₀) N.state_open (hDH Q₀) (hH Q₀) hR hRN hND a.normal a.normal_unit hgap₀
  let r₀ := (S - R) / 2
  have hr₀ : 0 < r₀ := half_pos (sub_pos.mpr hRS)
  have hsmallS : closedBall z₀ r₀ ⊆ closedBall (0, ξ) S := by
    intro z hz
    have hd := dist_triangle z z₀ (0, ξ)
    have hz' := mem_closedBall.mp hz
    have hz₀' := mem_closedBall.mp hzR
    change dist z (0, ξ) ≤ S
    dsimp [r₀] at hz'
    linarith
  have hSD : closedBall (0, ξ) S ⊆ N.stateDomain :=
    (closedBall_subset_closedBall hSN.le).trans hND
  have hsmallN : closedBall z₀ r₀ ⊆ closedBall (0, ξ) N.stateRadius :=
    hsmallS.trans (closedBall_subset_closedBall hSN.le)
  obtain ⟨rf, bf, δf, Φf, Cf, Af, V, hrf, _hbf, hδf, hV, _hVc, hyV,
    hCft, _hCf, _hSf, F, C, hprops, hcont⟩ :=
    exists_commonBufferedHamiltonPhases_finiteOrder (H Q₀) N.state_open (hDH Q₀)
      (hH Q₀) a.embedding a.normal a.orthogonal a.spanning hr₀
      (hsmallS.trans hSD) henergy (hgap₀ z₀ hzR)
  have hmono (Q : _) (m : ℕ) :
      cNorm (closedBall z₀ r₀) m (fun z ↦ (H Q).h z - (H Q₀).h z) ≤
        cNorm (closedBall (0, ξ) N.stateRadius) m
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) :=
    cNorm_mono_set_of_contDiffAt hsmallN (isCompact_closedBall _ _)
      (fun z hz ↦ (((hH Q).sub (hH Q₀)).contDiffAt
        (N.state_open.mem_nhds (hND hz))).of_le (by simp))
  let E := {J : HomogeneousSymbol (Euclidean n) // N.stateDomain ⊆ J.domain ∧
    ContDiffOn ℝ ∞ J.h N.stateDomain ∧ cNorm (closedBall z₀ r₀) 3
      (fun z ↦ J.h z - (H Q₀).h z) ≤ δf}
  let J₀ : E := ⟨H Q₀, hDH Q₀, hH Q₀, by
    simp only [sub_self]; exact (cNorm_zero _ _).le.trans hδf.le⟩
  have hzero : EqOn (C J₀).coordinates Cf.coordinates V := by
    intro z hz
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨d, hd, hb⟩ := hcont {z} isCompact_singleton (singleton_subset_iff.mpr hz) 0 ε hε
    have hc := hb J₀ (by simp only [J₀, sub_self]; exact (cNorm_zero _ _).trans_lt hd)
    have hc' := (le_add_of_nonneg_right (cNorm_nonneg {z} 0
      (fun z ↦ phase (C J₀).coordinates z - phase Cf.coordinates z))).trans_lt hc
    simpa only [cNorm_order_zero, image_singleton, csSup_singleton, Pi.sub_apply,
      zero_add] using hc'.le
  obtain ⟨e, he, heV⟩ := Metric.isOpen_iff.mp hV _ hyV
  let η := min (3 * L.sourceRadius) (3 * rf) /
    (2 * (‖(A.symm : (Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ]
      (ℝ × InitialData (Euclidean (n - 1))))‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let ρ := min L.radius (min e η) / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρL : 2 * ρ < L.radius := by
    have := min_le_left L.radius (min e η); dsimp [ρ]; linarith
  have hρe : 2 * ρ < e := by
    have := (min_le_right L.radius (min e η)).trans (min_le_left e η)
    dsimp [ρ]; linarith
  have hρη : 2 * ρ < η := by
    have := (min_le_right L.radius (min e η)).trans (min_le_right e η)
    dsimp [ρ]; linarith
  let W := ball (a.embedding a.baseData.1, a.baseData.2) (2 * ρ)
  have hWV : W ⊆ V := (ball_subset_ball hρe.le).trans heV
  have heq (Q : _) (J : E) (hJ : J.1 = H Q)
      (hsmall : cNorm (closedBall (0, ξ) N.stateRadius) 3
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δg) :
      EqOn (L.chart Q).coordinates (C J).coordinates W := by
    obtain ⟨_ht, _hp, hj, hCt, hCs, _hbuf, _hC, _hS, _hi, _ho, _hh, hadm, hr⟩ := hprops J
    have hstate : ∀ q ∈ (F J).time ×ˢ (F J).parameters,
        ((F J).position q, (F J).momentum q) ∈ closedBall (0, ξ) S :=
      fun q hq ↦ hsmallS (hr q hq)
    have hsrc : (L.chart Q).source ⊆ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
      rw [L.source_eq]; exact inter_subset_left
    cases J with
    | mk J hJprop =>
      dsimp only at hJ
      subst J
      have hh := (L.chart Q).coordinates_eq_on_transverse_overlap (C ⟨H Q, hJprop⟩)
        N.state_open (hDH Q) (hH Q) hSD a.embedding a.normal hν a.orthogonal a.spanning
        (L.section_eq Q) hj (hgap (H Q) (hDH Q) (hH Q) hsmall)
        (by positivity : 0 < 3 * L.sourceRadius) (by positivity : 0 < 3 * rf)
        A (L.source_admissible Q) hadm hsrc (by simpa only [hCt] using hCs)
        (hhalf Q) (fun q hq ↦ closedBall_subset_closedBall hRS.le (hrange Q q hq)) hstate
      intro z hz
      exact hh ⟨⟨L.target_contains Q (ball_subset_ball (by linarith) hz),
        hCt.symm ▸ hWV hz⟩, ball_subset_ball hρη.le hz⟩
  have heq₀ : EqOn (L.chart Q₀).coordinates Cf.coordinates W := by
    have hh := heq Q₀ J₀ rfl (by simp only [sub_self, cNorm_zero]; exact hδg)
    exact fun z hz ↦ (hh hz).trans (hzero (hWV hz))
  refine ⟨ρ, hρ, hρL, ?_⟩
  intro K hK hKW m ε hε
  obtain ⟨d, hd, hc⟩ := hcont K hK (hKW.trans hWV) m ε hε
  refine ⟨min δg (min δf d), lt_min hδg (lt_min hδf hd), ?_⟩
  intro Q hsmall
  have h₃ : cNorm (closedBall (0, ξ) N.stateRadius) 3
      (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < min δg (min δf d) :=
    (cNorm_mono_order (le_max_left _ _)).trans_lt hsmall
  let J : E := ⟨H Q, hDH Q, hH Q, (hmono Q 3).trans
    (h₃.le.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hcomp := hc J ((hmono Q (m + 1)).trans_lt
    ((cNorm_mono_order (le_max_right _ _)).trans_lt
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))))
  have heqQ := heq Q J rfl (h₃.trans_le (min_le_left _ _))
  have hec : cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) =
      cNorm K m ((C J).coordinates - Cf.coordinates) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds (hKW hz)] with y hy
    exact congrArg₂ (· - ·) (heqQ hy) (heq₀ hy)
  have hes : cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) =
      cNorm K m (fun z ↦ phase (C J).coordinates z - phase Cf.coordinates z) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds (hKW hz)] with y hy
    simp only [Pi.sub_apply, phase, heqQ hy, heq₀ hy]
  rw [hec, hes]
  exact hcomp

/-- The actual local-family producer discharges the source inverse gap and
transverse range of the positive-reference comparison. Every fixed member of
one retained family has finite-order continuity on a common open buffer;
neither its charts nor its reference are reselected (`app:lem:common-hamilton-phase`). -/
theorem exists_localQuantitativeFamily_with_positiveReference_comparison
    {n : ℕ} {ξ : Euclidean n} (hξ : ξ ≠ 0) (hchar : cubeDeterminant ξ = 0)
    (a : AdaptedSection ξ) (N : LocalFrozenReference a)
    (hgapN : ∀ q ∈ closedBall (0, ξ) N.stateRadius,
      ⟪(frozenSymbol n).hp q, a.normal⟫_ℝ ≠ 0)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hdomain : ∀ q ∈ N.stateDomain, q.1 ∈ U) :
    ∃ L : LocalQuantitativeFamily N U hU, ∀ Q₀,
      ∃ ρ > (0 : ℝ), 2 * ρ < L.radius ∧
        ∀ K : Set (Euclidean n × (ℝ × Euclidean (n - 1))),
          IsCompact K → K ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * ρ) →
          ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
            cNorm (closedBall (0, ξ) N.stateRadius) (max 3 (m + 1))
              (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
            cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
              cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε := by
  obtain ⟨L, R, A, hR, hRN, hg⟩ :=
    exists_localQuantitativeFamily_with_transverse_control hξ hchar a N hgapN hU hdomain
  exact ⟨L, fun Q₀ ↦ exists_retained_positiveReference_comparison hdomain L hR hRN A
    (fun Q ↦ (hg Q).2.1) (fun Q ↦ (hg Q).2.2.1) Q₀ (hg Q₀).2.2.2.1⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
