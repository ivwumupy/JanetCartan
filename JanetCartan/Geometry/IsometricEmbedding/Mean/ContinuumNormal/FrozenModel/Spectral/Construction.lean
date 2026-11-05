module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CanonicalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.ConicInverse

/-!
# Construct the local frozen inverse from the retained Hamilton family

The exact geometric inputs used by the frozen spectral leaves are produced
from the original immersion hypotheses. All radii, thresholds, reference
charts and determinant gaps precede the immersion. This supplies the local
geometric construction in `app:ch_background:prop:bg-frame`; finite incidence
coverage, coefficient regularity, integrability and spectral positivity remain
separate obligations of the final assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Actual construction of the zero-scale conic inverse, its domain and
Jacobian gap for the SAME retained Hamilton chart. Only the original seed
incidence/transversality and immersion hypotheses are used. The normalized
forward map and both inverse identities are proved, not assumed
(`new:lem:scaling`, `app:ch_background:eq:bg-Psi`, `bg-jacobian`). -/
theorem exists_frozen_conic_inputs {c C : ℝ} (hP : P.IsValid c C)
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
      6 * a < T.family.radius ∧ 3 * r < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
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
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          V L b cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤
              (angularWidth ηb r / 4) * ‖u.2‖) ∧
        IsOpen (frozenSymbolDomain T Q z₀ ηb r (6 * a)) ∧
        Measurable (frozenSymbolInverse T Q z₀ ηb r (6 * a)) ∧
        ContDiffOn ℝ ∞ (frozenSymbolInverse T Q z₀ ηb r (6 * a))
          (frozenSymbolDomain T Q z₀ ηb r (6 * a)) ∧
        EqOn (augmentedTransportGradient (normalizedTransportPosition T Q 0) ∘
          inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a))) id
            (frozenSymbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ p ∈ frozenInputDomain z₀ ηb r (6 * a),
          inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a))
            (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
        (∀ p ∈ frozenInputDomain z₀ ηb r (6 * a),
          0 < transportAbsoluteJacobian (adaptedSliceCoordinates T)
            (normalizedTransportPosition T Q 0) p) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r, hr, a, ha, hacap, har, haR, hphys, hcarrier, δ₀, hδ₀, cJ, hcJ,
    b, hb, V, L, hV, hVc, hLc, hLV, hlocal⟩ :=
    exists_actual_local_charts T hP hz₀ hk hinc hd (N := N) hKF hKU hball C₀ hκmet hκ hcap
  obtain ⟨δ₁, hδ₁, htrans⟩ := exists_supported_transverse_threshold T hP z₀ hηb hr hphys hcarrier
  refine ⟨r, hr, a, ha, hacap, har, haR, hphys, hcarrier,
    min δ₀ δ₁, lt_min hδ₀ hδ₁, cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
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
  have har' : 6 * a ≤ 3 * r := by linarith
  exact ⟨hf, hgap, hInv, htrans',
    frozenSymbolDomain_open T Q hηb hr hInv htrans' hV hLV,
    frozenSymbolInverse_measurable T Q hηb hr hInv htrans' hV hLV,
    frozenSymbolInverse_smooth T Q hηb hr hInv htrans' hLV,
    augmentedFrozenGradient_inverse T Q hP hηb hr har' hcarrier hInv htrans',
    fun _ hp ↦ frozenInverse_augmentedGradient T Q hP hηb hr har' hcarrier hInv htrans' hp,
    fun _ hp ↦ frozenJacobian_pos T Q hP hηb hr har' hcarrier hInv htrans' hf hcJ hp⟩

end JanetCartan.ContinuumNormal.FrozenModel
