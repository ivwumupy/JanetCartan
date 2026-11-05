module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.Momentum
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.JointFlow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.InverseComparison

/-!
# Hamilton comparison on the original retained coefficient compact

The prescribed coefficient compact maps into the ORIGINAL target. Direct
root, ODE and inverse estimates compare the same retained transport position
in order `m + 2` and carrier gradient in order `m` on this compact. No central
radius is reselected. The actual forward smoothness and all initial-section,
ODE and inverse-range inputs are proved for the retained family.

`exists_originalCoefficient_carrier_immersion_tolerance` composes this
comparison with the actual projected-frame and normalized-symbol estimates.
It preserves input order `max 8 (m + 5)` and proves frame admission. Its
consumer is `RetainedLeading.exists_originalScalar_primitives_sub_tolerance`,
for `app:lem:common-hamilton-phase`, `app:ch_background:prop:bg-frame` and
`app:ch_background:prop:bg-normalized`. Final primitive and seed/history
assembly remains with that consumer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference
open ContinuumRow CanonicalCarrier ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The prescribed coefficient compact has a compact Hamilton image inside
the ORIGINAL retained target. In particular, this applies to the original
coefficient ball exported by `exists_full_leading_originalScalar_chart_before_budgets`,
with its already selected parameter center (`app:lem:common-hamilton-phase`). -/
theorem originalCoefficient_hamiltonCompact {c C : ℝ} (hP : P.IsValid c C)
    {KP : Set (Euclidean n × Euclidean 3)} (hKP : IsCompact KP)
    (hKPO : KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    IsCompact (T.carrierRestriction '' KP) ∧ T.carrierRestriction '' KP ⊆ T.target := by
  refine ⟨hKP.image_of_continuousOn ((T.carrierRestriction_smooth hP).continuousOn.mono hKPO), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact T.target_contains_closed (hKPO hp).1 (fun i ↦ ((hKPO hp).2 i).le)

variable
  (hdomain : ∀ z ∈ T.data.localReference.stateDomain, z.1 ∈ U)
  (hgeometry : ∃ (R : ℝ)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1)))),
    0 < R ∧ R < T.data.localReference.stateRadius ∧
    (∀ Q, ∀ q ∈ ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (T.family.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
    (∀ Q, ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
      ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
        closedBall (0, T.data.center) R) ∧
    (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      ∀ z ∈ closedBall (0, T.data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0))

include hdomain hgeometry

/-- Order-zero comparison of the SAME retained position and gradient on the
prescribed original coefficient and carrier compacts. Its hypotheses are
exactly the retained producer geometry and compact containments; all root,
trajectory, inverse and momentum comparisons are discharged. This is the
base case, not the requested `C^(m+2)` position estimate, for
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_originalCoefficient_carrier_zero_symbol_tolerance
    {c C : ℝ} (hP : P.IsValid c C) (Q₀ : _)
    {KP : Set (Euclidean n × Euclidean 3)} (hKP : IsCompact KP)
    (hKPO : KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S KP)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, T.data.center) T.data.localReference.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm S 0 (transportPosition T Q - transportPosition T Q₀) +
        cNorm KP 0 (fun p ↦ T.carrierGradient Q p.1 p.2 - T.carrierGradient Q₀ p.1 p.2) < ε := by
  let J := T.carrierRestriction '' KP
  obtain ⟨hJ, hJT⟩ := originalCoefficient_hamiltonCompact T hP hKP hKPO
  have hJbig : J ⊆ ball (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) (2 * T.family.radius) :=
    hJT.trans (ball_subset_ball (by linarith [T.family.radius_pos]))
  obtain ⟨R, A, hR, hRN, hhalf, hrange, hgap⟩ := hgeometry
  obtain ⟨Bc, hBc, hcoord⟩ := exists_retained_coordinates_sub_le_symbol
    hdomain T.family hR hRN A hhalf hrange Q₀ (hgap Q₀)
  obtain ⟨Bp, dp, hBp, hdp, hmomentum⟩ := exists_retained_chartMomentum_sub_le_symbol
    hdomain T.family hR hRN A hhalf hrange Q₀ (hgap Q₀) hJ hJbig
  have hSO : S ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    exact ⟨(hKPO (hSK hp)).1, (hKPO (hSK hp)).2⟩
  have hmap : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      T.carrierRestriction (p.1, parameter p.2)) S J :=
    fun p hp ↦ mem_image_of_mem _ (hSK hp)
  obtain ⟨DX, hDX, hX⟩ := PositiveReference.exists_transportPosition_sub_le_coordinates
    T hP (K := S) (L := J) hS hJ hSO hJT hmap
  have hD : 0 < DX 0 * Bc + Bp := add_pos (mul_pos (hDX 0) hBc) hBp
  refine ⟨min dp (ε / (DX 0 * Bc + Bp)), lt_min hdp (div_pos hε hD), ?_⟩
  intro Q hsmall
  let e := cNorm (closedBall (0, T.data.center) T.data.localReference.stateRadius) 1
    (normalizedSymbol Q.1 - normalizedSymbol Q₀.1)
  have hc : cNorm J 0 ((T.family.chart Q).coordinates - (T.family.chart Q₀).coordinates) ≤
      Bc * e := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ Bc * e)
      (fun _ _ ↦ mul_nonneg hBc.le (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj z hz
    have hj₀ : j = 0 := by omega
    subst j
    simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hcoord Q z (hJbig hz)
  have hx : cNorm S 0 (transportPosition T Q - transportPosition T Q₀) ≤ DX 0 * (Bc * e) :=
    (hX Q Q₀ 0).trans (mul_le_mul_of_nonneg_left hc (hDX 0).le)
  have hp : cNorm KP 0 (fun p ↦ T.carrierGradient Q p.1 p.2 - T.carrierGradient Q₀ p.1 p.2) ≤
      Bp * e := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ Bp * e)
      (fun _ _ ↦ mul_nonneg hBp.le (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj p hp
    have hj₀ : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hgrad (Q : _) : T.carrierGradient Q p.1 p.2 =
        (T.family.chart Q).chartMomentum (T.carrierRestriction p) :=
      (hasGradientAt_carrierPhase (T.currentChart Q) T.reference.spatialPatch
        (T.carrierRestriction_mem_target Q (hKPO hp))).gradient
    rw [hgrad Q, hgrad Q₀]
    exact hmomentum Q (hsmall.trans_le (min_le_left _ _)) _ (mem_image_of_mem _ hp)
  have ht := (lt_div_iff₀ hD).mp (hsmall.trans_le (min_le_right _ _))
  change e * (DX 0 * Bc + Bp) < ε at ht
  calc
    _ ≤ DX 0 * (Bc * e) + Bp * e := add_le_add hx hp
    _ = e * (DX 0 * Bc + Bp) := by ring
    _ < ε := ht

/-- Scalar-symbol comparison of the SAME retained carrier fields on the
prescribed original coefficient and carrier compacts. The original target
contains the full Hamilton image, so no central radius is reselected. Symbol
order `m + 3` suffices for position order `m + 2` and gradient order `m`
(`app:lem:common-hamilton-phase`; `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_originalCoefficient_carrier_symbol_tolerance
    {c C : ℝ} (hP : P.IsValid c C) (Q₀ : _)
    {KP : Set (Euclidean n × Euclidean 3)} (hKP : IsCompact KP)
    (hKPO : KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S KP)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, T.data.center) T.data.localReference.stateRadius) (m + 3)
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm S (m + 2) (transportPosition T Q - transportPosition T Q₀) +
        cNorm KP m (fun p ↦ T.carrierGradient Q p.1 p.2 - T.carrierGradient Q₀ p.1 p.2) < ε := by
  let J := T.carrierRestriction '' KP
  obtain ⟨hJ, hJT⟩ := originalCoefficient_hamiltonCompact T hP hKP hKPO
  have hJbig : J ⊆ ball (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) (2 * T.family.radius) :=
    hJT.trans (ball_subset_ball (by linarith [T.family.radius_pos]))
  have hSO : S ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    exact ⟨(hKPO (hSK hp)).1, (hKPO (hSK hp)).2⟩
  have hmap : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      T.carrierRestriction (p.1, parameter p.2)) S J :=
    fun p hp ↦ mem_image_of_mem _ (hSK hp)
  obtain ⟨DX, hDX, hX⟩ := PositiveReference.exists_transportPosition_sub_le_coordinates
    T hP (K := S) (L := J) hS hJ hSO hJT hmap
  obtain ⟨DP, hDP, hPbound⟩ := PositiveReference.exists_carrierGradient_sub_le_phase
    T hP hKP hJ hKPO hJT (fun p hp ↦ mem_image_of_mem _ hp)
  have hD : 0 < DX (m + 2) + DP m := add_pos (hDX _) (hDP _)
  obtain ⟨R, A, hR, hRN, hhalf, hrange, hgap⟩ := hgeometry
  obtain ⟨δ, hδ, hc⟩ := exists_retained_originalTarget_coordinates_phase_tolerance
    T.family hdomain hR hRN A hhalf hrange Q₀ (hgap Q₀) hJ hJbig
      (m + 2) (div_pos hε hD)
  refine ⟨δ, hδ, ?_⟩
  intro Q hsmall
  have hh := hc Q hsmall
  have hx := hX Q Q₀ (m + 2)
  have hp := hPbound Q Q₀ m
  have hmono : cNorm J (m + 1)
      (phase (T.currentChart Q).coordinates - phase (T.currentChart Q₀).coordinates) ≤
        cNorm J (m + 2)
          (phase (T.family.chart Q).coordinates - phase (T.family.chart Q₀).coordinates) :=
    cNorm_mono_order (by omega)
  have hh' := (lt_div_iff₀ hD).mp hh
  change cNorm S (m + 2) (transportPosition T Q - transportPosition T Q₀) ≤
    DX (m + 2) * cNorm J (m + 2)
      ((T.family.chart Q).coordinates - (T.family.chart Q₀).coordinates) at hx
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hmono (hDP m).le)
  have hnC := cNorm_nonneg J (m + 2)
    ((T.family.chart Q).coordinates - (T.family.chart Q₀).coordinates)
  have hnS := cNorm_nonneg J (m + 2)
    (phase (T.family.chart Q).coordinates - phase (T.family.chart Q₀).coordinates)
  nlinarith [hDX (m + 2), hDP m]

/-- Immersion-only comparison on the ORIGINAL retained coefficient compact
and any prescribed compact carrier set mapping into it. The reference
smoothness, immersion, full normal rank, order-four budget and separate
positive metric/normal gaps are preserved, and admission of the actual
varying projected frame is proved. The finite input order is exactly
`max 8 (m + 5)`. This is the Hamilton input to
`exists_originalScalar_primitives_sub_tolerance`
(`app:ch_background:prop:bg-frame`; `app:ch_background:prop:bg-normalized`;
`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_originalCoefficient_carrier_immersion_tolerance
    {c C : ℝ} (hP : P.IsValid c C) {N : ℕ} (Q₀ : _)
    {F₀ : Euclidean n → Euclidean N} (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U) (hrank₀ : HasFullNormalRankOn F₀ U)
    (hQ₀ : Q₀.1 = projectedStress F₀)
    {C₀ κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F₀ ≤ C₀)
    (hmet₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ w ∈ normalSpace F₀ x, κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    {KP : Set (Euclidean n × Euclidean 3)} (hKP : IsCompact KP)
    (hKPO : KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S KP)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean N,
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ C₀ →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (m + 5)) (F - F₀) < δ →
      ∃ (hQ : ContDiffOn ℝ ∞ (projectedStress F) U)
        (hadm : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold),
        cNorm S (m + 2) (transportPosition T ⟨projectedStress F, hQ, hadm⟩ -
          transportPosition T Q₀) +
        cNorm KP m (fun p ↦ T.carrierGradient ⟨projectedStress F, hQ, hadm⟩ p.1 p.2 -
          T.carrierGradient Q₀ p.1 p.2) < ε := by
  have hball : closedBall (0, T.data.center) T.data.localReference.stateRadius ⊆
      T.data.localReference.stateDomain := by
    simpa only [T.data.adapted.baseState_eq] using T.data.localReference.stateBall_subset
  have hKU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U := by
    intro x hx
    apply hdomain (x, T.data.center)
    apply hball
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hx
  have hproj : MapsTo Prod.fst (closedBall (0, T.data.center) T.data.localReference.stateRadius)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) := by
    intro z hz
    exact (show dist z.1 0 ≤ dist z (0, T.data.center) by
      rw [Prod.dist_eq]; exact le_max_left _ _).trans hz
  have hzero : ∀ z ∈ closedBall ((0 : Euclidean n), T.data.center) T.data.localReference.stateRadius,
      z.2 ≠ 0 := fun z hz ↦ (mem_frozenSymbol_domain z).mp
        (T.data.localReference.state_subset (hball hz))
  have hmargin : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F₀ - fun _ ↦ cubeStress n) < T.family.threshold := hQ₀ ▸ Q₀.2.2
  obtain ⟨da, hda, ha⟩ := PositiveReference.exists_admissible_projectedStress_sub_tolerance
    (isCompact_closedBall _ _) hU hKU hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀
    hnormal₀ hmargin 0 zero_lt_one
  obtain ⟨d, hd, hb⟩ := exists_originalCoefficient_carrier_symbol_tolerance
    T hdomain hgeometry hP Q₀ hKP hKPO hS hSK m hε
  obtain ⟨ds, hds, hs⟩ := PositiveReference.exists_projected_normalizedSymbol_sub_tolerance
    (isCompact_closedBall _ _) (isCompact_closedBall _ _) hU hKU hproj hzero hF₀ hi₀
    hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ (m + 3) hd
  refine ⟨min da ds, lt_min hda hds, ?_⟩
  intro F hF hi hrank hlow hmet hnormal hsmall
  have hadm := (ha F hF hi hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 8 (0 + 2) ≤ max 8 (m + 5))).trans_lt
      (hsmall.trans_le (min_le_left _ _)))).1
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  refine ⟨hQ, hadm, hb ⟨projectedStress F, hQ, hadm⟩ ?_⟩
  rw [hQ₀]
  exact hs F hF hi hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : m + 3 + 2 ≤ max 8 (m + 5))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
