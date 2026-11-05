module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.PrimitiveComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison

/-!
# Immersion comparison of the original retained primitives

Compose the original-compact Hamilton estimate with the actual ODE and normal
estimates. The maps, minor and original initial scalar are prescribed by the
retained producer. Consumer: the same-family weighted density comparison in
`FamilyInputs`, for `app:ch_background:prop:bg-frame` and
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}

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

/-- The SAME transport position, original normal, full reduced coefficient and
actual ODE density footpoint vary with the immersion. All primitive differences
are proved from the sole smallness assumption of order `max 8 (m + 6)`. The
original `R / 8` scalar domain, separate metric/normal gaps and retained
coefficient compact are preserved. Source: `app:ch_osc:prop:osc-normal`, Step 4',
`app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`. -/
theorem exists_originalScalar_immersion_sub_tolerance
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hKFU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hx : MapsTo Prod.fst K (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    {S : Set (Euclidean n × CarrierParameter)} (hS : IsCompact S)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) S K)
    (hSflow : MapsTo (densityCoordinates T) S
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    {F₀ : Euclidean n → Euclidean N}
    (c₀ : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F₀)
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (hrank₀ : HasFullNormalRankOn F₀ U)
    {M κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hlow₀ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F₀ ≤ M)
    (hmet₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F₀ x v‖ ^ 2)
    (hnormal₀ : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ w ∈ normalSpace F₀ x,
      κnormal * ‖w‖ ≤ ‖normalPairing F₀ (fun _ ↦ w) x‖)
    {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8)))
    (hipos : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) S
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) S
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (m + 6)) (F - F₀) < δ →
      cNorm S (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) +
        cNorm S m (c.normal initial - c₀.normal initial) +
        cNorm S m (c.reduced - c₀.reduced) +
        cNorm S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) < ε := by
  let KF := closedBall (0 : Euclidean n) T.data.localReference.stateRadius
  have hKF : IsCompact KF := isCompact_closedBall _ _
  obtain ⟨dp, hdp, hp⟩ := exists_originalScalar_primitives_sub_tolerance hP hΩ hK hKΩ
    hRc hB hτ hbuffer hτeq hKF hKFU hKU hx hS hSK hSflow c₀ hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀ m
      (half_pos hε)
  have hKPO : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius) := fun p hp ↦ ⟨(hKU hp).1.2, (hKU hp).2⟩
  have he : 0 < min (ε / 2) (dp / 3) := lt_min (half_pos hε) (by positivity)
  obtain ⟨dh, hdh, hh⟩ := exists_originalCoefficient_carrier_immersion_tolerance
    T hdomain hgeometry hP c₀.Q hF₀ hi₀ hrank₀ c₀.frame_eq hκmet hκnormal
    hlow₀ hmet₀ hnormal₀ hK hKPO hS hSK (m + 1) he
  have hmargin : cNorm KF 6 (projectedStress F₀ - fun _ ↦ cubeStress n) <
      T.family.threshold := c₀.frame_eq ▸ c₀.Q.2.2
  obtain ⟨dq, hdq, hq⟩ := exists_admissible_projectedStress_sub_tolerance
    hKF hU hKFU hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀
    hmargin (m + 1) (show 0 < dp / 3 by positivity)
  refine ⟨min dh (min dq (dp / 3)), lt_min hdh (lt_min hdq (by positivity)), ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall
  have hham := hh F hF him hrank hlow hmet hnormal
    (by simpa only [Nat.add_assoc] using hsmall.trans_le (min_le_left _ _))
  obtain ⟨hQ, hadm, hham⟩ := hham
  have hQc : (⟨projectedStress F, hQ, hadm⟩ : _) = c.Q :=
    Subtype.ext c.frame_eq.symm
  rw [hQc] at hham
  have hgrad : cNorm K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2) < dp / 3 := by
    have := cNorm_nonneg S (m + 1 + 2) (transportPosition T c.Q - transportPosition T c₀.Q)
    have := hham.trans_le (min_le_right _ _)
    linarith
  have hpos : cNorm S (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) < ε / 2 := by
    have := cNorm_nonneg K (m + 1) (fun p ↦ T.carrierGradient c.Q p.1 p.2 -
      T.carrierGradient c₀.Q p.1 p.2)
    have ht := cNorm_mono_order (f := transportPosition T c.Q - transportPosition T c₀.Q)
      (s := S) (by omega : m + 2 ≤ m + 1 + 2)
    have := hham.trans_le (min_le_left _ _)
    linarith
  have hframe : cNorm KF (m + 1) (c.Q.1 - c₀.Q.1) < dp / 3 := by
    rw [c.frame_eq, c₀.frame_eq]
    exact (hq F hF him hrank hlow hmet hnormal
      ((cNorm_mono_order (by omega : max 8 (m + 1 + 2) ≤ max 8 (m + 6))).trans_lt
        (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))))).2
  have himm : cNorm KF (m + 2) (F - F₀) < dp / 3 :=
    (cNorm_mono_order (by omega : m + 2 ≤ max 8 (m + 6))).trans_lt
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hprims := hp F c hF him hrank hlow hmet hnormal hfoot
    (by linarith only [hframe, hgrad, himm])
  linarith only [hpos, hprims]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
