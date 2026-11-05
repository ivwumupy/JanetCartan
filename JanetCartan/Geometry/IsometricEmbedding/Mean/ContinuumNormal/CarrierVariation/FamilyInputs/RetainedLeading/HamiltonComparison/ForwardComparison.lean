module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.ForwardRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.RootContinuity

/-!
# Finite-order comparison of the original forward projection

The actual root and joint ODE estimates are assembled on any compact ball
strictly inside the original source ball. Scalar symbol order `m + 1`
controls forward order `m`, preserving the finite derivative reserve in
`app:lem:common-hamilton-phase`. The consumer is the inverse comparison on
the original retained target compact.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ} {N : LocalFrozenReference a}
  {U : Set (Euclidean n)} {hU : IsOpen U}
  (L : LocalQuantitativeFamily N U hU)
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

set_option maxHeartbeats 1000000 in
/-- Finite-order comparison of the SAME retained forward augmented
projections on any prescribed compact source ball, using only one additional
scalar-symbol derivative. All initial-section, ODE, smoothness and range
premises are discharged for the given family (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_forward_compact_tolerance {r : ℝ}
    (hr : 0 < r) (hrT : r < 3 * L.sourceRadius)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm (closedBall ((0 : ℝ), a.baseData) r) m
        ((L.flow Q).augmentedProjection - (L.flow Q₀).augmentedProjection) < ε := by
  let H (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold}) :=
    normalizedHomogeneousSymbol hU Q.1 Q.2.1
  let T := 3 * L.sourceRadius
  let Ψ (Q : _) : InitialData (Euclidean (n - 1)) × ℝ → Euclidean n × Euclidean n :=
    fun q ↦ ((L.flow Q).position (q.2, q.1), (L.flow Q).momentum (q.2, q.1))
  have hND : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  have hRD : closedBall (0, ξ) R ⊆ N.stateDomain :=
    (closedBall_subset_closedBall hRN.le).trans hND
  have hDH (Q : _) : N.stateDomain ⊆ (H Q).domain := fun z hz ↦
    ⟨hdomain z hz, (mem_frozenSymbol_domain z).mp (N.state_subset hz)⟩
  have hH (Q : _) : ContDiffOn ℝ ∞ (H Q).h N.stateDomain :=
    (contDiffOn_normalizedSymbol hU Q.2.1).mono (hDH Q)
  have hV (Q : _) : ContDiffOn ℝ ∞ (H Q).vectorField N.stateDomain :=
    (H Q).contDiffOn_vectorField_of_subset N.state_open (hDH Q) (by simpa using hH Q)
  have hswap (s : InitialData (Euclidean (n - 1))) (t : ℝ)
      (hs : s ∈ ball a.baseData T) (ht : t ∈ Ioo (-T) T) :
      (t, s) ∈ ball ((0 : ℝ), a.baseData) T := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht hs
  have hadm (Q : _) (s) (hs : s ∈ ball a.baseData T) (t) (ht : t ∈ Ioo (-T) T) :=
    L.source_admissible Q (hswap s t hs ht)
  have hΨ (Q : _) : ContDiffOn ℝ ∞ (Ψ Q) (ball a.baseData T ×ˢ Ioo (-T) T) :=
    (retained_state_smooth L hdomain Q).comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun q hq ↦ hswap q.1 q.2 hq.1 hq.2)
  have hode (Q : _) (s) (hs : s ∈ ball a.baseData T) (t) (ht : t ∈ Ioo (-T) T) :
      HasDerivAt (fun τ ↦ Ψ Q (s, τ)) ((H Q).vectorField (Ψ Q (s, t))) t :=
    ((L.flow Q).position_hasDerivAt (hadm Q s hs t ht).1 (hadm Q s hs t ht).2).prodMk
      ((L.flow Q).momentum_hasDerivAt (hadm Q s hs t ht).1 (hadm Q s hs t ht).2)
  have hΨrange (Q : _) (s) (hs : s ∈ closedBall a.baseData r) (t) (ht : t ∈ Ioo (-T) T) :
      Ψ Q (s, t) ∈ closedBall (0, ξ) R :=
    hrange Q _ (hadm Q s (closedBall_subset_ball hrT hs) t ht)
  let B : (Euclidean n × Euclidean n) →L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))) :=
    (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).prod 0
  let C : ℝ := (m + 1 : ℝ) * (‖B‖ + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d, hd, hjoint⟩ := exists_retained_joint_flow_tolerance
    N.state_open hR hRD (hV Q₀) (hΨ Q₀) (hode Q₀) (hΨrange Q₀)
    hr hrT hr hrT m (div_pos hε hC)
  obtain ⟨di, hdi, hinitial⟩ := exists_retained_initialState_compact_tolerance
    L hdomain hR hRN hrange Q₀ hgap₀ (isCompact_closedBall _ _)
      (closedBall_subset_ball hrT) m (half_pos hd)
  have hm : 0 < (m + 1 : ℝ) := by positivity
  refine ⟨min di (d / (2 * (m + 1 : ℝ))), lt_min hdi (div_pos hd (by positivity)), ?_⟩
  intro Q hsmall
  let e := cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
    (normalizedSymbol Q.1 - normalizedSymbol Q₀.1)
  have hfield : cNorm (closedBall (0, ξ) R) m ((H Q).vectorField - (H Q₀).vectorField) ≤
      (m + 1 : ℝ) * e := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ e)
      (fun _ _ ↦ cNorm_nonneg _ _ _) ?_).trans_eq (by simp)
    intro j hj z hz
    exact (norm_iteratedFDeriv_vectorField_sub_le (H Q) (H Q₀) N.state_open
      (hDH Q) (hDH Q₀) ((hH Q).of_le (by simp)) ((hH Q₀).of_le (by simp)) (hRD hz)).trans
      (norm_symbol_jet_sub_le_cNorm (H Q) (H Q₀) N.state_open
        ((hH Q).of_le (by simp)) ((hH Q₀).of_le (by simp)) (isCompact_closedBall _ _)
        hND (by omega : j + 1 ≤ m + 1) (closedBall_subset_closedBall hRN.le hz))
  have hfsmall : cNorm (closedBall (0, ξ) R) m
      ((H Q).vectorField - (H Q₀).vectorField) < d / 2 := by
    apply hfield.trans_lt
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (m + 1 : ℝ))).mp
      (hsmall.trans_le (min_le_right _ _))
    change e * (2 * (m + 1 : ℝ)) < d at hh
    nlinarith
  have hjoint' := hjoint (H Q).vectorField (Ψ Q) (hV Q) (hΨ Q) (hode Q) (hΨrange Q)
    (by
      have hi := hinitial Q (hsmall.trans_le (min_le_left _ _))
      change cNorm (closedBall a.baseData r) m (fun s ↦ Ψ Q (s, 0) - Ψ Q₀ (s, 0)) < d / 2 at hi
      linarith)
  let K := closedBall a.baseData r ×ˢ Icc (-r) r
  let f := Ψ Q - Ψ Q₀
  let E := LinearIsometryEquiv.prodComm ℝ ℝ (InitialData (Euclidean (n - 1)))
  have heq : (L.flow Q).augmentedProjection - (L.flow Q₀).augmentedProjection = B ∘ (f ∘ E) := by
    funext q
    simp [HamiltonFlow.augmentedProjection, B, f, E, Ψ]
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKO : K ⊆ ball a.baseData T ×ˢ Ioo (-T) T := by
    intro q hq
    exact ⟨closedBall_subset_ball hrT hq.1, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
  have hf : ∀ q ∈ K, ContDiffAt ℝ m f q := fun q hq ↦
    (((hΨ Q).sub (hΨ Q₀)).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds (hKO hq))).of_le
      (by simp)
  have hmap : MapsTo E (closedBall ((0 : ℝ), a.baseData) r) K := by
    intro q hq
    have hh : |q.1| ≤ r ∧ dist q.2 a.baseData ≤ r := by
      simpa only [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right,
        Real.norm_eq_abs] using hq
    exact ⟨hh.2, abs_le.mp hh.1⟩
  rw [heq]
  have hb : cNorm (closedBall ((0 : ℝ), a.baseData) r) m (B ∘ (f ∘ E)) ≤
      (m + 1 : ℝ) * (‖B‖ * cNorm K m f) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ ‖B‖ * cNorm K m f)
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj q hq
    apply (B.norm_iteratedFDeriv_comp_left
      ((hf _ (hmap hq)).comp q E.contDiff.contDiffAt) (by exact_mod_cast hj)).trans
    rw [E.norm_iteratedFDeriv_comp_right]
    exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf (hmap hq) hj) (norm_nonneg _)
  have hh := (lt_div_iff₀ hC).mp hjoint'
  change cNorm K m f * C < ε at hh
  exact hb.trans_lt (by dsimp [C] at hh; nlinarith [cNorm_nonneg K m f])

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
