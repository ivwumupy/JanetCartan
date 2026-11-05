module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.LowOrder

/-!
# Finite-order comparison of the retained initial roots

For `app:lem:common-hamilton-phase`, the initial momentum of the original
Hamilton flow is itself a smooth transverse root. Local implicit-equation
estimates apply to that root, with its range supplied by the already proved
order-zero trajectory comparison. Compactness combines these local estimates
on any prescribed compact in the original parameter ball. The consumer is
the retained forward-flow comparison on the original source buffer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ} {N : LocalFrozenReference a}
  {U : Set (Euclidean n)} {hU : IsOpen U}
  (L : LocalQuantitativeFamily N U hU)

/-- The normal component of the SAME retained initial momentum, rather than
a newly chosen root (`app:lem:common-hamilton-phase`). -/
def retainedSectionRoot (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold}) (s : InitialData (Euclidean (n - 1))) : ℝ :=
  ⟪a.normal, (L.flow Q).momentum (0, s)⟫_ℝ

/-- The retained scalar root reconstructs the actual initial state, throughout
the original parameter ball (`app:lem:common-hamilton-phase`). -/
theorem retainedSectionRoot_state (Q : _) {s : InitialData (Euclidean (n - 1))}
    (hs : s ∈ ball a.baseData (3 * L.sourceRadius)) :
    transverseSectionState a.embedding a.normal (s, retainedSectionRoot L Q s) =
      ((L.flow Q).position (0, s), (L.flow Q).momentum (0, s)) := by
  have hs' : (0, s) ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    exact hs
  have hp := (L.source_admissible Q hs').2
  have hν : a.normal ≠ 0 := by
    intro he
    have hh := a.normal_unit
    rw [he, norm_zero] at hh
    norm_num at hh
  have he := sectionMomentum_eq_normal_add_tangent a.embedding a.normal
    ((L.flow Q).momentum (0, s)) hν a.orthogonal a.spanning s.2.2 (by
      simpa only [L.section_eq, LinearIsometry.coe_toContinuousLinearMap] using
        (L.flow Q).initial_momentum s hp)
  have hunit : ⟪a.normal, a.normal⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, a.normal_unit]
    norm_num
  apply Prod.ext
  · simpa only [transverseSectionState, L.section_eq,
      LinearIsometry.coe_toContinuousLinearMap] using ((L.flow Q).initial_position s hp).symm
  · simpa only [transverseSectionState, retainedSectionRoot, hunit, div_one] using he.symm

/-- Smoothness of the retained root follows from the retained momentum, on
the entire original parameter ball (`app:lem:common-hamilton-phase`). -/
theorem retainedSectionRoot_smooth (Q : _) :
    ContDiffOn ℝ ∞ (retainedSectionRoot L Q) (ball a.baseData (3 * L.sourceRadius)) := by
  have hm : ContDiffOn ℝ ∞ (fun s ↦ (L.flow Q).momentum (0, s))
      (ball a.baseData (3 * L.sourceRadius)) := by
    apply (L.momentum_smooth Q).comp (contDiffOn_const.prodMk contDiffOn_id)
    intro s hs
    apply L.source_admissible Q
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    exact hs
  exact contDiffOn_const.inner ℝ hm

variable
  (hdomain : ∀ z ∈ N.stateDomain, z.1 ∈ U)
  {R : ℝ} (hR : 0 < R) (hRN : R < N.stateRadius)
  (hrange : ∀ Q, ∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
    ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R)
  (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold})
  (hgap₀ : ∀ z ∈ closedBall (0, ξ) R,
    ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0)

include hdomain hR hRN hrange hgap₀

/-- Uniform value comparison for the retained roots on the original parameter
ball. This supplies their range in each local transverse cylinder, without an
assumed root comparison (`app:lem:common-hamilton-phase`). -/
theorem exists_retainedSectionRoot_sub_le_symbol :
    ∃ B > (0 : ℝ), ∀ Q, ∀ s ∈ ball a.baseData (3 * L.sourceRadius),
      |retainedSectionRoot L Q s - retainedSectionRoot L Q₀ s| ≤
        B * cNorm (closedBall (0, ξ) N.stateRadius) 1
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
  obtain ⟨B, hB, hb⟩ := exists_retained_state_sub_le_symbol
    hdomain L hR hRN hrange Q₀ hgap₀
  refine ⟨B, hB, ?_⟩
  intro Q s hs
  have hs' : (0, s) ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    exact hs
  have hi := abs_real_inner_le_norm a.normal
    ((L.flow Q).momentum (0, s) - (L.flow Q₀).momentum (0, s))
  rw [a.normal_unit, one_mul, inner_sub_right] at hi
  exact hi.trans ((norm_snd_le
    (((L.flow Q).position (0, s), (L.flow Q).momentum (0, s)) -
      ((L.flow Q₀).position (0, s), (L.flow Q₀).momentum (0, s)))).trans (hb Q _ hs'))

/-- At each point of the original parameter ball, the actual retained roots
have finite-order symbol continuity on a fixed neighborhood. The root range is
proved from value comparison; it is not an additional premise
(`app:lem:common-hamilton-phase`). -/
theorem exists_retainedSectionRoot_local_tolerance
    {s₀ : InitialData (Euclidean (n - 1))}
    (hs₀ : s₀ ∈ ball a.baseData (3 * L.sourceRadius)) :
    ∃ r > (0 : ℝ), ball s₀ (2 * r) ⊆ ball a.baseData (3 * L.sourceRadius) ∧
      ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
        cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
        cNorm (closedBall s₀ r) m (retainedSectionRoot L Q - retainedSectionRoot L Q₀) < ε := by
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
  have hadm (Q : _) (s : _) (hs : s ∈ ball a.baseData (3 * L.sourceRadius)) :
      (0, s) ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters := by
    apply L.source_admissible Q
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
    exact hs
  have henergy (Q : _) (s : _) (hs : s ∈ ball a.baseData (3 * L.sourceRadius)) :
      (H Q).h (transverseSectionState a.embedding a.normal (s, retainedSectionRoot L Q s)) =
        s.2.1 := by
    rw [retainedSectionRoot_state L Q hs]
    exact (L.flow Q).initial_energy s (hadm Q s hs).2
  let τ₀ := retainedSectionRoot L Q₀ s₀
  let W := transverseSectionState a.embedding a.normal ⁻¹' ball (0, ξ) N.stateRadius
  have hW : IsOpen W := isOpen_ball.preimage
    (contDiff_transverseSectionState a.embedding a.normal).continuous
  have hbase : (s₀, τ₀) ∈ W := by
    change transverseSectionState a.embedding a.normal (s₀, τ₀) ∈ ball (0, ξ) N.stateRadius
    rw [show τ₀ = retainedSectionRoot L Q₀ s₀ from rfl, retainedSectionRoot_state L Q₀ hs₀]
    exact closedBall_subset_ball hRN (hrange Q₀ _ (hadm Q₀ s₀ hs₀))
  have hf : ContDiffOn ℝ ∞ (sectionEnergyEquation (H Q₀) a.embedding a.normal) W :=
    ((hH Q₀).comp (contDiff_transverseSectionState a.embedding a.normal).contDiffOn
      (fun _ hz ↦ hND (ball_subset_closedBall hz))).sub contDiffOn_fst.snd.fst
  have hzero : sectionEnergyEquation (H Q₀) a.embedding a.normal (s₀, τ₀) = 0 :=
    sub_eq_zero.mpr (henergy Q₀ s₀ hs₀)
  have htrans : CharacteristicRoot.scalarDerivative
      (sectionEnergyEquation (H Q₀) a.embedding a.normal) (s₀, τ₀) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation (H Q₀) a.embedding a.normal
      (hDH Q₀ (hND (ball_subset_closedBall hbase)))]
    apply hgap₀
    rw [show τ₀ = retainedSectionRoot L Q₀ s₀ from rfl, retainedSectionRoot_state L Q₀ hs₀]
    exact hrange Q₀ _ (hadm Q₀ s₀ hs₀)
  obtain ⟨r₀, b, c, e, hr₀, hb, hc, _he, hmap, hgap, _hend⟩ :=
    CharacteristicRoot.exists_simple_root_cylinder hW hf hbase hzero htrans
  have hnear : ∀ᶠ s in 𝓝 s₀, s ∈ ball a.baseData (3 * L.sourceRadius) ∧
      |retainedSectionRoot L Q₀ s - τ₀| < b / 2 := by
    have hcont := ((retainedSectionRoot_smooth L Q₀).contDiffAt
      (isOpen_ball.mem_nhds hs₀)).continuousAt
    filter_upwards [isOpen_ball.mem_nhds hs₀,
      (hcont.sub continuousAt_const).abs.eventually_lt continuousAt_const
        (show |retainedSectionRoot L Q₀ s₀ - τ₀| < b / 2 by
          simpa only [τ₀, sub_self, abs_zero] using half_pos hb)] with s hs ht
    exact ⟨hs, ht⟩
  obtain ⟨t, ht, hnear⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min r₀ (t / 3)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrt : 2 * r < t := by
    have hh := min_le_right r₀ (t / 3)
    dsimp [r]
    linarith
  have hnear' (s : _) (hs : s ∈ ball s₀ (2 * r)) :
      s ∈ ball a.baseData (3 * L.sourceRadius) ∧
        |retainedSectionRoot L Q₀ s - τ₀| < b / 2 :=
    hnear (ball_subset_ball hrt.le hs)
  have hmap' : MapsTo (transverseSectionState a.embedding a.normal)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - b) (τ₀ + b))
      (closedBall (0, ξ) N.stateRadius) := by
    intro z hz
    exact ball_subset_closedBall (hmap
      ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩)
  have hgap' : ∀ z ∈ closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - b) (τ₀ + b),
      2 * c ≤ |CharacteristicRoot.scalarDerivative
        (sectionEnergyEquation (H Q₀) a.embedding a.normal) z| := by
    intro z hz
    exact hgap z ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩
  have hg (Q : _) : ContDiffOn ℝ ∞ (retainedSectionRoot L Q) (ball s₀ (2 * r)) :=
    (retainedSectionRoot_smooth L Q).mono (fun s hs ↦ (hnear' s hs).1)
  obtain ⟨B, hB, hvalue⟩ := exists_retainedSectionRoot_sub_le_symbol
    L hdomain hR hRN hrange Q₀ hgap₀
  refine ⟨r, hr, (fun s hs ↦ (hnear' s hs).1), ?_⟩
  intro m ε hε
  obtain ⟨d, hd, hroot⟩ := exists_sectionRoot_finiteOrder_tolerance
    (H Q₀) a.embedding a.normal N.state_open (isCompact_closedBall _ _) hND (hH Q₀)
    hr hc hmap' (hg Q₀) hgap' (fun s hs ↦
      ⟨by
        have hh := abs_lt.mp (hnear' s hs).2
        constructor <;> linarith [hh.1, hh.2], henergy Q₀ s (hnear' s hs).1⟩) m hε
  refine ⟨min d (b / (2 * B)), lt_min hd (div_pos hb (by positivity)), ?_⟩
  intro Q hsmall
  apply hroot (H Q) (retainedSectionRoot L Q) (hH Q) (hg Q) ?_
    (hsmall.trans_le (min_le_left _ _))
  intro s hs
  refine ⟨?_, henergy Q s (hnear' s hs).1⟩
  have hval := hvalue Q s (hnear' s hs).1
  have hsm : cNorm (closedBall (0, ξ) N.stateRadius) 1
      (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < b / (2 * B) :=
    (cNorm_mono_order (by omega : 1 ≤ m + 1)).trans_lt
      (hsmall.trans_le (min_le_right _ _))
  have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * B)).mp hsm
  have hdiff : |retainedSectionRoot L Q s - retainedSectionRoot L Q₀ s| < b / 2 := by
    nlinarith
  have htri := abs_sub_le (retainedSectionRoot L Q s) (retainedSectionRoot L Q₀ s) τ₀
  have habs : |retainedSectionRoot L Q s - τ₀| < b := by
    linarith [(hnear' s hs).2]
  have hh := abs_lt.mp habs
  constructor <;> linarith [hh.1, hh.2]

/-- Finite-order comparison of the SAME retained section roots on any
prescribed compact inside the original parameter ball. The compact need not
lie in a newly centered reference chart. A finite cover combines the actual
local root equations with their proved range control. Symbol order `m + 1`
is sufficient (`app:lem:common-hamilton-phase`). -/
theorem exists_retainedSectionRoot_compact_tolerance
    {K : Set (InitialData (Euclidean (n - 1)))} (hK : IsCompact K)
    (hKO : K ⊆ ball a.baseData (3 * L.sourceRadius))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm K m (retainedSectionRoot L Q - retainedSectionRoot L Q₀) < ε := by
  classical
  choose r hr hsub hcont using fun s : K ↦
    exists_retainedSectionRoot_local_tolerance L hdomain hR hRN hrange Q₀ hgap₀ (hKO s.2)
  obtain ⟨I, hcover⟩ := hK.elim_finite_subcover (fun s : K ↦ ball s.1 (r s))
    (fun _ ↦ isOpen_ball) (fun s hs ↦ mem_iUnion.mpr
      ⟨⟨s, hs⟩, mem_ball_self (hr ⟨s, hs⟩)⟩)
  let e := ε / (2 * (m + 1 : ℝ))
  have he : 0 < e := div_pos hε (by positivity)
  choose d hd hb using fun s : K ↦ hcont s m e he
  have hmin : ∃ δ > (0 : ℝ), ∀ s ∈ I, δ ≤ d s := by
    clear hcover
    induction I using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert s I _ ih =>
      obtain ⟨δ, hδ, hb⟩ := ih
      refine ⟨min (d s) δ, lt_min (hd s) hδ, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb t ht)
  obtain ⟨δ, hδ, hδd⟩ := hmin
  refine ⟨δ, hδ, ?_⟩
  intro Q hsmall
  have hjet : ∀ j ≤ m, ∀ s ∈ K,
      ‖iteratedFDeriv ℝ j (retainedSectionRoot L Q - retainedSectionRoot L Q₀) s‖ ≤ e := by
    intro j hj s hs
    obtain ⟨t, ht, hst⟩ := mem_iUnion₂.mp (hcover hs)
    have hsm := hb t Q (hsmall.trans_le (hδd t ht))
    have hsmooth : ∀ u ∈ closedBall t.1 (r t),
        ContDiffAt ℝ m (retainedSectionRoot L Q - retainedSectionRoot L Q₀) u := by
      intro u hu
      have huO := hsub t (closedBall_subset_ball (by linarith [hr t] : r t < 2 * r t) hu)
      exact (((retainedSectionRoot_smooth L Q).sub (retainedSectionRoot_smooth L Q₀)).contDiffAt
        (isOpen_ball.mem_nhds huO)).of_le (by simp)
    exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      hsmooth (ball_subset_closedBall hst) hj).trans hsm.le
  have hn := cNorm_le_sum_of_bounds (fun _ _ ↦ he.le) hjet
  have heq : (∑ _j ∈ Finset.range (m + 1), e) = (m + 1 : ℝ) * e := by simp
  rw [heq] at hn
  have hmul := (div_mul_cancel₀ ε (by positivity : (2 * (m + 1 : ℝ)) ≠ 0))
  change e * (2 * (m + 1 : ℝ)) = ε at hmul
  nlinarith

/-- The original retained initial state has finite-order symbol continuity
on every prescribed compact parameter set. This supplies the varying initial
jets in the differentiated ODE comparison; symbol order `m + 1` is preserved
(`app:lem:common-hamilton-phase`). -/
theorem exists_retained_initialState_compact_tolerance
    {K : Set (InitialData (Euclidean (n - 1)))} (hK : IsCompact K)
    (hKO : K ⊆ ball a.baseData (3 * L.sourceRadius))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm K m (fun s ↦
        ((L.flow Q).position (0, s), (L.flow Q).momentum (0, s)) -
        ((L.flow Q₀).position (0, s), (L.flow Q₀).momentum (0, s))) < ε := by
  let V : ℝ →L[ℝ] (Euclidean n × Euclidean n) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (0, a.normal)
  let C := (m + 1 : ℝ) * (‖V‖ + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨δ, hδ, hb⟩ := exists_retainedSectionRoot_compact_tolerance
    L hdomain hR hRN hrange Q₀ hgap₀ hK hKO m (div_pos hε hC)
  refine ⟨δ, hδ, ?_⟩
  intro Q hsmall
  let g := retainedSectionRoot L Q - retainedSectionRoot L Q₀
  have hg : ∀ s ∈ K, ContDiffAt ℝ m g s := by
    intro s hs
    exact (((retainedSectionRoot_smooth L Q).sub (retainedSectionRoot_smooth L Q₀)).contDiffAt
      (isOpen_ball.mem_nhds (hKO hs))).of_le (by simp)
  have heq : ∀ s ∈ K, (fun s ↦
      ((L.flow Q).position (0, s), (L.flow Q).momentum (0, s)) -
      ((L.flow Q₀).position (0, s), (L.flow Q₀).momentum (0, s))) =ᶠ[𝓝 s] V ∘ g := by
    intro s hs
    filter_upwards [isOpen_ball.mem_nhds (hKO hs)] with u hu
    rw [← retainedSectionRoot_state L Q hu, ← retainedSectionRoot_state L Q₀ hu]
    simp [V, g, transverseSectionState, sub_smul]
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq heq m]
  have hbound : cNorm K m (V ∘ g) ≤ (m + 1 : ℝ) * (‖V‖ * cNorm K m g) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ ‖V‖ * cNorm K m g)
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj s hs
    apply (V.norm_iteratedFDeriv_comp_left (hg s hs) (by exact_mod_cast hj)).trans
    exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg hs hj) (norm_nonneg _)
  have hsmallg : cNorm K m g < ε / C := hb Q hsmall
  have hmul := (lt_div_iff₀ hC).mp hsmallg
  have hn := cNorm_nonneg K m g
  dsimp [C] at hmul
  nlinarith

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
