module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.JacobianRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.MaskContainment

/-!
# The actual supported conic inverse

The local projected-stress charts and the stronger primitive transverse
comparison instantiate `ConicChart.AnnularData`. Its completed generic
construction then gives injectivity on the whole supported cone and the
actual inverse with degree-zero incidence and degree-one covector scaling.
No conic chart or inverse conclusion is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier
open ContinuumNormalReduction.ConicChart ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct the actual conic inverse for each physical/spectator slice.
Every radius and primitive closeness threshold precedes the immersion. The
inverse is supplied by the already proved annular normalization construction;
the annular hypotheses are proved here for the retained Hamilton family.
The joint conic inverse is smooth on its proved open image and has a global
measurable extension. Both Jacobian comparisons and degree-one scaling are
proved, with uniform positive constants chosen before the immersion. The
physical `6a` buffer contains the original measurement support at `4a`.
Source: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`. -/
theorem exists_actual_conic_inverse {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ} {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    {cap : ℝ} (hcap : 0 < cap) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), 6 * a < cap ∧ 6 * a ≤ r ∧
      6 * a < T.family.radius ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ CJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ C₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
              ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G ∧
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a) ×ˢ
            supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)) ∧
        IsOpen (supportedOutput T Q z₀ ηb r (6 * a)) ∧
        ContDiffOn ℝ ∞ (conicInverse T Q z₀ ηb r (6 * a))
          (supportedOutput T Q z₀ ηb r (6 * a)) ∧
        Measurable (conicInverse T Q z₀ ηb r (6 * a)) ∧
        (∀ q ∈ supportedOutput T Q z₀ ηb r (6 * a),
          conicInverse T Q z₀ ηb r (6 * a) q ∈
            supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r) ∧
          adaptedTransportChart T Q q.1 (conicInverse T Q z₀ ηb r (6 * a) q) = q.2 ∧
          ∀ t : ℝ, 0 < t →
            conicInverse T Q z₀ ηb r (6 * a) (q.1, t • q.2) =
              radialScale t (conicInverse T Q z₀ ηb r (6 * a) q)) ∧
        IsOpen (symbolDomain T Q z₀ ηb r (6 * a)) ∧
        ContDiffOn ℝ ∞ (symbolInverse T Q z₀ ηb r (6 * a))
          (symbolDomain T Q z₀ ηb r (6 * a)) ∧
        Measurable (symbolInverse T Q z₀ ηb r (6 * a)) ∧
        MapsTo (ContinuumNormalReduction.TransportSymbol.inverseCoordinates
          (symbolInverse T Q z₀ ηb r (6 * a)))
          (symbolDomain T Q z₀ ηb r (6 * a)) (symbolInputDomain z₀ ηb r (6 * a)) ∧
        EqOn (ContinuumNormalReduction.TransportSymbol.augmentedTransportGradient
          (transportPosition T Q) ∘ ContinuumNormalReduction.TransportSymbol.inverseCoordinates
            (symbolInverse T Q z₀ ηb r (6 * a))) id (symbolDomain T Q z₀ ηb r (6 * a)) ∧
        EqOn (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)) ∘
          augmentedTransportGradient (transportPosition T Q)) id (symbolInputDomain z₀ ηb r (6 * a)) ∧
        ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q))
          (symbolInputDomain z₀ ηb r (6 * a)) ∧
        (∀ p ∈ symbolInputDomain z₀ ηb r (6 * a),
          0 < transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p) ∧
        (∀ p ∈ symbolInputDomain z₀ ηb r (6 * a), ∀ t : ℝ, 0 < t →
          transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) (scaleInput t p) =
            t * transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q) p) ∧
        (∀ p ∈ symbolInputDomain z₀ ηb r (6 * a),
          inner ℝ (transportPosition T Q (p.1.1, p.2.1)) p.2.2 -
            inner ℝ (transportPosition T Q (p.1.2, p.2.1)) p.2.2 =
            inner ℝ (p.1.1 - p.1.2) (transportAveragedGradient (transportPosition T Q) p)) ∧
        ∀ p ∈ physicalParameterSet z₀ (6 * a),
          ∃ A : AnnularData (Euclidean (n - 1)),
            A.map = adaptedTransportChart T Q p ∧
            A.cone = supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r) ∧
            InjOn (adaptedTransportChart T Q p) A.cone ∧
            (∀ u ∈ A.cone, A.inverse (adaptedTransportChart T Q p u) = u) ∧
            (∀ ξ ∈ adaptedTransportChart T Q p '' A.cone,
              adaptedTransportChart T Q p (A.inverse ξ) = ξ) ∧
            (∀ ξ ∈ adaptedTransportChart T Q p '' A.cone, ∀ t : ℝ, 0 < t →
              A.inverse (t • ξ) = ((A.inverse ξ).1, t • (A.inverse ξ).2)) ∧
            (∀ ξ ∈ adaptedTransportChart T Q p '' A.cone,
              conicInverse T Q z₀ ηb r (6 * a) (p, ξ) = A.inverse ξ) ∧
            (∀ u ∈ A.cone,
              (cJ / ‖ηb‖) * ‖u.2‖ ≤ adaptedJacobian T Q p u ∧
              adaptedJacobian T Q p u ≤ (CJ / ‖ηb‖) * ‖u.2‖) ∧
            (∀ u ∈ A.cone, ∀ t : ℝ, 0 < t →
              adaptedJacobian T Q p (radialScale t u) = t * adaptedJacobian T Q p u) ∧
            (∀ u ∈ A.cone,
              (1 - angularWidth ηb r / 4) * ‖u.2‖ ≤ ‖adaptedTransportChart T Q p u‖ ∧
              ‖adaptedTransportChart T Q p u‖ ≤ CJ * ‖u.2‖) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r, hr, a, ha, hacap, har, haR, hphys, hcarrier, δ₀, hδ₀, cJ, hcJ,
    b, hb, V, L, hV, hVc, hLc, hLV, hlocal⟩ :=
    exists_actual_local_charts T hP hz₀ hk hinc hd (N := N) hKF hKU hball C₀ hκmet hκ hcap
  obtain ⟨δ₁, hδ₁, htrans⟩ := exists_supported_transverse_threshold T hP z₀ hηb hr hphys hcarrier
  obtain ⟨CJ, hCJ, hCJbound⟩ := exists_reference_differential_upper
    (FrozenIncidence.referenceEquiv T hP hz₀ hinc hd)
  refine ⟨r, hr, a, ha, hacap, har, haR, hcarrier, min δ₀ δ₁, lt_min hδ₀ hδ₁,
    cJ, hcJ, CJ, hCJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨ProjectedStressFrame.projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  obtain ⟨hf, hgap, hInv, _⟩ := hlocal F hF hi hrank hlowF hmet hnormal hlow
    (hclose.trans_le (min_le_left _ _))
  have htrans' : ∀ p ∈ physicalParameterSet z₀ (6 * a),
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖ := by
    intro p hp
    exact htrans Q (hclose.trans_le (min_le_right _ _)) p
      ⟨ball_subset_ball har hp.1, ball_subset_ball har hp.2.1, ball_subset_ball har hp.2.2⟩
  refine ⟨hf, hgap, hInv, adaptedTransportChart_smooth_on_cone T Q hηb hr hf,
    supportedOutput_open T Q hηb hr hInv htrans' hV hLV,
    conicInverse_smooth T Q hηb hr hInv htrans' hLV,
    conicInverse_measurable T Q hηb hr hInv htrans' hV hLV, ?_,
    symbolDomain_open T Q hηb hr hInv htrans' hV hLV,
    symbolInverse_smooth T Q hηb hr hInv htrans' hLV,
    symbolInverse_measurable T Q hηb hr hInv htrans' hV hLV,
    symbolInverse_maps T Q hηb hr hInv htrans',
    augmentedTransportGradient_symbolInverse T Q hηb hr hInv htrans',
    fun _ hp ↦ symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans' hp,
    transportAbsoluteJacobian_smooth T Q hηb hr hf hInv htrans' hcJ,
    fun _ hp ↦ transportAbsoluteJacobian_pos T Q hηb hr hf hInv htrans' hcJ hp,
    fun _ hp _ ht ↦ transportAbsoluteJacobian_scaling T Q hηb hr hf hInv htrans' hp ht,
    fun _ hp ↦ phase_identity_on_symbolInputDomain T Q hP hr haR
      (har.trans (by linarith)) hcarrier hp, ?_⟩
  · intro q hq
    rw [conicInverse_eq T Q hq]
    refine ⟨localConicInverse_mem T Q hηb hr hInv htrans' hq,
      map_localConicInverse T Q hηb hr hInv htrans' hq, ?_⟩
    intro t ht
    rw [conicInverse_eq T Q ((supportedOutput_smul_iff T Q ht q).mpr hq)]
    exact localConicInverse_smul T Q hηb hr hInv htrans' hq ht
  · intro p hp
    let A := supportedAnnularData T Q z₀ hηb hr p (hInv.injective p hp) (htrans' p hp)
    refine ⟨A, rfl, rfl, A.injective_on_cone, fun _ hu ↦ A.inverse_map hu,
      fun _ hξ ↦ A.map_inverse hξ, fun _ hξ _ ht ↦ A.inverse_smul hξ ht, ?_, ?_, ?_, ?_⟩
    · intro ξ hξ
      have hξ' : (p, ξ) ∈ supportedOutput T Q z₀ ηb r (6 * a) := ⟨hp, hξ⟩
      rw [conicInverse_eq T Q hξ']
      obtain ⟨u, hu, rfl⟩ := hξ
      rw [localConicInverse_map T Q hηb hr hInv htrans' hp hu]
      exact (A.inverse_map hu).symm
    · exact fun _ hu ↦ adaptedJacobian_bounds T Q hηb hr hf hInv htrans' hgap
        (fun D hD ↦ (hCJbound D hD).2) hp hu
    · exact fun _ hu _ ht ↦ adaptedJacobian_radialScale T Q hηb hr hf hInv htrans' hp hu ht
    · exact fun _ hu ↦ adaptedTransportChart_norm_bounds T Q hηb hr hf hInv htrans' hgap
        (fun D hD ↦ (hCJbound D hD).1) hp hu

end JanetCartan.ContinuumRow.CanonicalConic
