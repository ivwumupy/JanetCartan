module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.ForwardComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.OriginalTarget

/-!
# Finite-order comparison on the original retained target

For `app:lem:common-hamilton-phase`, the original half gap and the proved
source buffer allow differentiated inverse comparison on every prescribed
compact in the original target. The forward estimate concerns the same
retained maps and costs exactly one scalar-symbol derivative. The consumer
is the carrier comparison on the original coefficient compact.
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
  (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
    (Euclidean n × (ℝ × Euclidean (n - 1))))
  (hhalf : ∀ Q, ∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
    ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
      ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
  (hrange : ∀ Q, ∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
    ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R)
  (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold})
  (hgap₀ : ∀ z ∈ closedBall (0, ξ) R,
    ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0)

include hdomain hR hRN hhalf hrange hgap₀

set_option maxHeartbeats 1000000 in
/-- Finite-order comparison of the SAME retained coordinates and phase on
any prescribed compact in the ORIGINAL target. No target radius is
reselected, and no chart or forward continuity is assumed. Scalar order
`m + 1` suffices for output order `m` (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_originalTarget_coordinates_phase_tolerance
    {J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hJ : IsCompact J)
    (hJT : J ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) (m + 1)
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm J m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
        cNorm J m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε := by
  let V := ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius)
  let D := ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius)
  let g (Q : _) := chartLift (L.chart Q).coordinates
  have hg (Q : _) : ContDiffOn ℝ ∞ (g Q) V :=
    (L.coordinates_smooth Q).fst.prodMk ((L.coordinates_smooth Q).snd.prodMk contDiffOn_snd)
  have hf (Q : _) : ContDiffOn ℝ ∞ (L.flow Q).augmentedProjection D :=
    (retained_state_smooth L hdomain Q).fst.prodMk contDiffOn_snd.snd
  have heq (Q : _) : EqOn ((L.flow Q).augmentedProjection ∘ g Q) id V :=
    fun z hz ↦ Prod.ext ((L.chart Q).right_inverse z (L.target_contains Q hz)) rfl
  obtain ⟨r, d₀, hr, hrT, hd₀, hbuffer⟩ := exists_retained_originalTarget_source_buffer
    hdomain L hR hRN A hhalf hrange Q₀ hgap₀ hJ hJT
  have hzero : cNorm (closedBall (0, ξ) N.stateRadius) 1
      (normalizedSymbol Q₀.1 - normalizedSymbol Q₀.1) < d₀ := by
    simpa only [sub_self, cNorm_zero] using hd₀
  let P : (ℝ × InitialData (Euclidean (n - 1))) →L[ℝ] (ℝ × Euclidean (n - 1)) :=
    (ContinuousLinearMap.fst ℝ ℝ (InitialData (Euclidean (n - 1)))).prod
      ((ContinuousLinearMap.fst ℝ (Euclidean (n - 1)) (ℝ × Euclidean (n - 1))).comp
        (ContinuousLinearMap.snd ℝ ℝ (InitialData (Euclidean (n - 1)))))
  obtain ⟨B, hB, hphase⟩ := exists_phase_finiteOrder_bound hJ m
  let C : ℝ := (1 + B) * (m + 1 : ℝ) * (‖P‖ + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨di, hdi, hinverse⟩ := InverseContinuity.exists_inverse_continuity_of_compact
    (isCompact_closedBall ((0 : ℝ), a.baseData) r) (convex_closedBall _ _) hJ
    isOpen_ball (closedBall_subset_ball hrT) isOpen_ball hJT (hf Q₀) (hg Q₀) A
    (fun z hz ↦ ball_subset_closedBall (hbuffer Q₀ hzero hz)) (heq Q₀) m (div_pos hε hC)
  obtain ⟨df, hdf, hforward⟩ := exists_retained_forward_compact_tolerance
    L hdomain hR hRN hrange Q₀ hgap₀ hr hrT m hdi
  refine ⟨min d₀ df, lt_min hd₀ hdf, ?_⟩
  intro Q hsmall
  have hlow := (cNorm_mono_order (by omega : 1 ≤ m + 1)).trans_lt
    (hsmall.trans_le (min_le_left _ _))
  have hi := hinverse (L.flow Q).augmentedProjection (g Q) (hf Q) (hg Q)
    (fun z hz ↦ ball_subset_closedBall (hbuffer Q hlow hz)) (heq Q) (hhalf Q)
    (hforward Q (hsmall.trans_le (min_le_right _ _)))
  have hproj : (L.chart Q).coordinates - (L.chart Q₀).coordinates = P ∘ (g Q - g Q₀) := by
    funext z
    exact Prod.ext rfl rfl
  have hc : cNorm J m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) ≤
      (m + 1 : ℝ) * (‖P‖ * cNorm J m (g Q - g Q₀)) := by
    rw [hproj]
    have hs : ∀ z ∈ J, ContDiffAt ℝ m (g Q - g Q₀) z := fun z hz ↦
      (((hg Q).sub (hg Q₀)).contDiffAt (isOpen_ball.mem_nhds (hJT hz))).of_le (by simp)
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ ‖P‖ * cNorm J m (g Q - g Q₀))
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj z hz
    exact (P.norm_iteratedFDeriv_comp_left (hs z hz) (by exact_mod_cast hj)).trans
      (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ hs hz hj) (norm_nonneg _))
  have hs := hphase V (L.chart Q).coordinates (L.chart Q₀).coordinates isOpen_ball hJT
    ((L.coordinates_smooth Q).of_le (by simp)) ((L.coordinates_smooth Q₀).of_le (by simp))
  have hs' : cNorm J m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) ≤
      B * cNorm J m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) := by
    convert! hs using 1
  have hi' := (lt_div_iff₀ hC).mp hi
  have hcg : cNorm J m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) ≤
      ((m + 1 : ℝ) * (‖P‖ + 1)) * cNorm J m (g Q - g Q₀) := by
    nlinarith [cNorm_nonneg J m (g Q - g Q₀)]
  have hm := mul_le_mul_of_nonneg_left hcg (show 0 ≤ 1 + B by linarith)
  dsimp [C] at hi'
  nlinarith only [hs', hm, hi']

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
