module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ImmersionComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficientBounds

/-!
# Primitive immersion continuity of the actual normal and phase covector

The physical density mean needs the actual covector, not merely its reduced
quadratic image. The original Hamilton estimate and the fixed linear carrier
coordinate map supply that covector estimate, on the same retained compact.
The normal is the original transported scalar normal. Consumer: the finite
physical mean tolerance in `app:ch_background:prop:bg-current`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalDensityContinuity

open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction HamiltonPhase ProjectedStressFrame
open RetainedLeading

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

include hdomain hgeometry in
/-- Both actual coefficient differences follow from the sole immersion jet
difference, using the original scalar domain and original retained compact.
The finite order is `max 8 (m + 6)`; no normal or covector difference is a premise. -/
theorem exists_retained_normal_covector_sub_tolerance
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
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) S
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (m + 6)) (F - F₀) < δ →
      cNorm S m (c.normal initial - c₀.normal initial) +
        cNorm S m (fun p ↦ T.carrierGradient c.Q p.1 (parameter p.2) -
          T.carrierGradient c₀.Q p.1 (parameter p.2)) < ε := by
  let L : (Euclidean n × CarrierParameter) →L[ℝ] (Euclidean n × Euclidean 3) :=
    (ContinuousLinearMap.id ℝ (Euclidean n)).prodMap parameter
  let cost := AmplitudeTame.linearNormCost L m
  have hcost : 0 < cost := AmplitudeTame.linearNormCost_pos L m
  have hKPO : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) :=
    fun p hp ↦ ⟨(hKU hp).1.2, (hKU hp).2⟩
  obtain ⟨dn, hdn, hn⟩ := exists_originalScalar_immersion_sub_tolerance T hdomain hgeometry
    hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx hS hSK hSflow c₀ hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀ m (half_pos hε)
  obtain ⟨dξ, hdξ, hξ⟩ := exists_originalCoefficient_carrier_immersion_tolerance T hdomain hgeometry
    hP c₀.Q hF₀ hi₀ hrank₀ c₀.frame_eq hκmet hκnormal hlow₀ hmet₀ hnormal₀
    hK hKPO hS hSK m (div_pos (half_pos hε) hcost)
  refine ⟨min dn dξ, lt_min hdn hdξ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall
  have hnAll := hn F c hF him hrank hlow hmet hnormal hfoot
    (hsmall.trans_le (min_le_left _ _))
  have hnSmall : cNorm S m (c.normal initial - c₀.normal initial) < ε / 2 := by
    have h₁ := cNorm_nonneg S (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q)
    have h₂ := cNorm_nonneg S m (c.reduced - c₀.reduced)
    have h₃ := cNorm_nonneg S m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)
    linarith only [hnAll, h₁, h₂, h₃]
  obtain ⟨hQ, hadm, hHamilton⟩ := hξ F hF him hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 8 (m + 5) ≤ max 8 (m + 6))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))
  have hQeq : (⟨projectedStress F, hQ, hadm⟩ : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = c.Q :=
    Subtype.ext c.frame_eq.symm
  rw [hQeq] at hHamilton
  let f := fun p : Euclidean n × Euclidean 3 ↦
    T.carrierGradient c.Q p.1 p.2 - T.carrierGradient c₀.Q p.1 p.2
  have hf : ContDiffOn ℝ ∞ f
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :=
    (T.carrierGradient_smooth hP c.Q).sub (T.carrierGradient_smooth hP c₀.Q)
  have hξK : cNorm K m f < (ε / 2) / cost := by
    have ht := cNorm_nonneg S (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q)
    change cNorm S (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) +
      cNorm K m f < (ε / 2) / cost at hHamilton
    linarith only [hHamilton, ht]
  have hpull := AmplitudeTame.cNorm_comp_linear_le L hK
    (isOpen_ball.prod (isOpen_parameterInterior _)) hKPO hf hSK m
  have hξSmall : cNorm S m (f ∘ L) < ε / 2 :=
    hpull.trans_lt ((mul_lt_mul_of_pos_left hξK hcost).trans_eq (mul_div_cancel₀ _ hcost.ne'))
  change cNorm S m (fun p ↦ T.carrierGradient c.Q p.1 (parameter p.2) -
    T.carrierGradient c₀.Q p.1 (parameter p.2)) < ε / 2 at hξSmall
  linarith only [hnSmall, hξSmall]

end JanetCartan.PhysicalDensityContinuity
