module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.RetainedComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.SymbolComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.CarrierDifferences

/-!
# Positive-reference dependence of the literal carrier fields

Consumer: `FamilyInputs.PositiveReference`, for `app:ch_background:prop:bg-frame`
and `app:ch_osc:prop:osc-normal`, Step 4'. The retained root/ODE/inverse comparison
is composed with primitive immersion-to-symbol continuity and the exact
transport-position and physical-gradient identities. The geometric witnesses
below are retained and discharged by the finite cover constructor in
`HamiltonDependence.Construction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference
open ContinuumRow CanonicalCarrier ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
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

/-- Scalar-symbol differences control the literal retained `transportPosition`
in order `m + 2` and `T.carrierGradient` in order `m`. All output compacts and
the open target precede the tolerance and varying frame. Geometric inputs are
exactly the witnesses of the actual frame producer, not continuity assumptions
(`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_retained_carrier_symbol_tolerance {c C : ℝ} (hP : P.IsValid c C)
    (Q₀ : _) :
    ∃ ρ > (0 : ℝ), 2 * ρ < T.family.radius ∧
      ∀ (KX : Set (Euclidean n × CarrierParameter))
        (KP : Set (Euclidean n × Euclidean 3))
        (J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))),
        IsCompact KX → IsCompact KP → IsCompact J →
        KX ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
          (parameter ⁻¹' parameterInterior (2 * P.radius)) →
        KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) →
        J ⊆ ball (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) (2 * ρ) →
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          T.carrierRestriction (p.1, parameter p.2)) KX J →
        MapsTo T.carrierRestriction KP J →
        ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
          cNorm (closedBall (0, T.data.center) T.data.localReference.stateRadius)
            (max 3 (m + 3)) (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
          cNorm KX (m + 2) (transportPosition T Q - transportPosition T Q₀) +
            cNorm KP m (fun p ↦ T.carrierGradient Q p.1 p.2 -
              T.carrierGradient Q₀ p.1 p.2) < ε := by
  obtain ⟨R, A, hR, hRN, hhalf, hrange, hgap⟩ := hgeometry
  obtain ⟨ρ, hρ, hρT, hcompare⟩ := exists_retained_positiveReference_comparison
    hdomain T.family hR hRN A hhalf hrange Q₀ (hgap Q₀)
  refine ⟨ρ, hρ, hρT, ?_⟩
  intro KX KP J hKX hKP hJ hKXO hKPO hJW hmapX hmapP m ε hε
  have hJT : J ⊆ T.target := hJW.trans (ball_subset_ball hρT.le)
  obtain ⟨DX, hDX, hX⟩ := exists_transportPosition_sub_le_coordinates T hP
    hKX hJ hKXO hJT hmapX
  obtain ⟨DP, hDP, hPbound⟩ := exists_carrierGradient_sub_le_phase T hP
    hKP hJ hKPO hJT hmapP
  have hD : 0 < DX (m + 2) + DP m := add_pos (hDX _) (hDP _)
  obtain ⟨δ, hδ, hc⟩ := hcompare J hJ hJW (m + 2) (ε / (DX (m + 2) + DP m))
    (div_pos hε hD)
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
  change cNorm KX (m + 2) (transportPosition T Q - transportPosition T Q₀) ≤
    DX (m + 2) * cNorm J (m + 2)
      ((T.family.chart Q).coordinates - (T.family.chart Q₀).coordinates) at hx
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hmono (hDP m).le)
  have hnC := cNorm_nonneg J (m + 2)
    ((T.family.chart Q).coordinates - (T.family.chart Q₀).coordinates)
  have hnS := cNorm_nonneg J (m + 2)
    (phase (T.family.chart Q).coordinates - phase (T.family.chart Q₀).coordinates)
  nlinarith [hDX (m + 2), hDP m]

/-- Primitive immersion differences control the SAME retained carrier position
and physical gradient at a fixed positive reference. The original immersion,
normal-rank, low budget and separate metric/normal gaps are preserved. The
strict frame margin is proved for the varying immersion. Input order is the
explicit finite `max 8 (m + 5)`, while all buffers precede `m`, `ε` and `F`
(`app:ch_background:prop:bg-frame`; `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_retained_carrier_immersion_tolerance {c C : ℝ} (hP : P.IsValid c C)
    {N : ℕ} (Q₀ : _)
    {F₀ : Euclidean n → Euclidean N} (hF₀ : ContDiffOn ℝ ∞ F₀ U)
    (hi₀ : IsImmersionOn F₀ U) (hrank₀ : HasFullNormalRankOn F₀ U)
    (hQ₀ : Q₀.1 = projectedStress F₀)
    {C₀ κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F₀ ≤ C₀)
    (hmet₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ w ∈ normalSpace F₀ x, κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖) :
    ∃ ρ > (0 : ℝ), 2 * ρ < T.family.radius ∧
      ∀ (KX : Set (Euclidean n × CarrierParameter))
        (KP : Set (Euclidean n × Euclidean 3))
        (J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))),
        IsCompact KX → IsCompact KP → IsCompact J →
        KX ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
          (parameter ⁻¹' parameterInterior (2 * P.radius)) →
        KP ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) →
        J ⊆ ball (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) (2 * ρ) →
        MapsTo (fun p : Euclidean n × CarrierParameter ↦
          T.carrierRestriction (p.1, parameter p.2)) KX J →
        MapsTo T.carrierRestriction KP J →
        ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ F : Euclidean n → Euclidean N, ContDiffOn ℝ ∞ F U →
            IsImmersionOn F U → HasFullNormalRankOn F U →
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
              cNorm KX (m + 2) (transportPosition T ⟨projectedStress F, hQ, hadm⟩ -
                transportPosition T Q₀) +
              cNorm KP m (fun p ↦ T.carrierGradient ⟨projectedStress F, hQ, hadm⟩ p.1 p.2 -
                T.carrierGradient Q₀ p.1 p.2) < ε := by
  obtain ⟨ρ, hρ, hρT, hc⟩ := exists_retained_carrier_symbol_tolerance T hdomain hgeometry hP Q₀
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
  obtain ⟨da, hda, ha⟩ := exists_admissible_projectedStress_sub_tolerance
    (isCompact_closedBall _ _) hU hKU hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀
    hnormal₀ hmargin 0 zero_lt_one
  refine ⟨ρ, hρ, hρT, ?_⟩
  intro KX KP J hKX hKP hJ hKXO hKPO hJW hmapX hmapP m ε hε
  obtain ⟨d, hd, hb⟩ := hc KX KP J hKX hKP hJ hKXO hKPO hJW hmapX hmapP m ε hε
  obtain ⟨ds, hds, hs⟩ := exists_projected_normalizedSymbol_sub_tolerance
    (isCompact_closedBall _ _) (isCompact_closedBall _ _) hU hKU hproj hzero hF₀ hi₀
    hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ (max 3 (m + 3)) hd
  refine ⟨min da ds, lt_min hda hds, ?_⟩
  intro F hF hi hrank hlow hmet hnormal hsmall
  have hadm := (ha F hF hi hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 8 (0 + 2) ≤ max 8 (m + 5))).trans_lt
      (hsmall.trans_le (min_le_left _ _)))).1
  have hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  refine ⟨hQ, hadm, hb ⟨projectedStress F, hQ, hadm⟩ ?_⟩
  rw [hQ₀]
  exact hs F hF hi hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 3 (m + 3) + 2 ≤ max 8 (m + 5))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
