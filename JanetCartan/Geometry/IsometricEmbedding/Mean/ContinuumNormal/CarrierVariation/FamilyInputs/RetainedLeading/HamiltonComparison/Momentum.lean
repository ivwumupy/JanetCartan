module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.OriginalTarget

/-!
# Momentum comparison on the original retained target compact

For `app:lem:common-hamilton-phase`, the actual inverse lifts stay in a compact
subset of the original source for sufficiently close symbols. Smoothness of
the reference momentum then transfers the retained trajectory comparison to
the chart momentum. The consumer is the order-zero carrier-gradient estimate
on the original coefficient compact in `HamiltonComparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

/-- The SAME retained chart momenta on an arbitrary compact in the original
target are locally Lipschitz in the scalar order-one symbol seminorm. The
common source buffer and reference momentum Lipschitz bound are proved from
the retained geometry, not added as assumptions
(`app:lem:common-hamilton-phase`; `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_retained_chartMomentum_sub_le_symbol {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} {N : LocalFrozenReference a}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hdomain : ∀ z ∈ N.stateDomain, z.1 ∈ U)
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
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0)
    {J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hJ : IsCompact J)
    (hJT : J ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius)) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      ∀ z ∈ J, ‖(L.chart Q).chartMomentum z - (L.chart Q₀).chartMomentum z‖ ≤
        B * cNorm (closedBall (0, ξ) N.stateRadius) 1
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
  obtain ⟨r, δ, _hr, hrL, hδ, hbuffer⟩ := exists_retained_originalTarget_source_buffer
    hdomain L hR hRN A hhalf hrange Q₀ hgap₀ hJ hJT
  obtain ⟨Bs, hBs, hstate⟩ := exists_retained_state_sub_le_symbol
    hdomain L hR hRN hrange Q₀ hgap₀
  obtain ⟨Bc, hBc, hcoord⟩ := exists_retained_coordinates_sub_le_symbol
    hdomain L hR hRN A hhalf hrange Q₀ hgap₀
  let K := closedBall ((0 : ℝ), a.baseData) r
  have hKsource : K ⊆ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) :=
    closedBall_subset_ball hrL
  have hm : ∀ q ∈ K, ContDiffAt ℝ 1 (L.flow Q₀).momentum q := by
    intro q hq
    exact ((L.momentum_smooth Q₀).contDiffAt
      (((L.flow Q₀).isOpen_time.prod (L.flow Q₀).isOpen_parameters).mem_nhds
        (L.source_admissible Q₀ (hKsource hq)))).of_le (by simp)
  let k : ℝ≥0 := ⟨cNorm K 1 (L.flow Q₀).momentum, cNorm_nonneg _ _ _⟩
  have hlip : LipschitzOnWith k (L.flow Q₀).momentum K := by
    apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq ↦ (hm q hq).differentiableAt (by simp))
    intro q hq
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      hm hq (le_refl 1)
    rw [norm_iteratedFDeriv_one] at hb
    exact_mod_cast hb
  refine ⟨Bs + k * Bc, δ, by positivity, hδ, ?_⟩
  intro Q hsmall z hz
  have hq : chartLift (L.chart Q).coordinates z ∈ K :=
    ball_subset_closedBall (hbuffer Q hsmall hz)
  have hq₀ : chartLift (L.chart Q₀).coordinates z ∈ K :=
    ball_subset_closedBall (hbuffer Q₀ (by simpa only [sub_self, cNorm_zero] using hδ) hz)
  have he : ‖chartLift (L.chart Q).coordinates z - chartLift (L.chart Q₀).coordinates z‖ =
      ‖(L.chart Q).coordinates z - (L.chart Q₀).coordinates z‖ := by
    simp [chartLift, Prod.norm_def]
  have hc := hlip.norm_sub_le hq hq₀
  rw [he] at hc
  have hs := (norm_snd_le
    (((L.flow Q).position (chartLift (L.chart Q).coordinates z),
      (L.flow Q).momentum (chartLift (L.chart Q).coordinates z)) -
     ((L.flow Q₀).position (chartLift (L.chart Q).coordinates z),
      (L.flow Q₀).momentum (chartLift (L.chart Q).coordinates z)))).trans
    (hstate Q _ (hKsource hq))
  calc
    _ ≤ ‖(L.flow Q).momentum (chartLift (L.chart Q).coordinates z) -
          (L.flow Q₀).momentum (chartLift (L.chart Q).coordinates z)‖ +
        ‖(L.flow Q₀).momentum (chartLift (L.chart Q).coordinates z) -
          (L.flow Q₀).momentum (chartLift (L.chart Q₀).coordinates z)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Bs * cNorm (closedBall (0, ξ) N.stateRadius) 1
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) +
        k * (Bc * cNorm (closedBall (0, ξ) N.stateRadius) 1
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1)) :=
      add_le_add hs (hc.trans (mul_le_mul_of_nonneg_left (hcoord Q z (hJT hz)) k.coe_nonneg))
    _ = _ := by ring

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
