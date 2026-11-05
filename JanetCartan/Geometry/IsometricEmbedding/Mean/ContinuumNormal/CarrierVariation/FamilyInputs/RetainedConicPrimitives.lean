module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ImmersionComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Conic primitive comparison for the retained leading scalar

Apply the proved immersion comparison to the same supplied ODE charts and
then to their actual Hamilton conic inverse and literal absolute Jacobian.
No inverse or Jacobian continuity is assumed. The common domains and gaps
are explicit geometric inputs from the conic construction; their simultaneous
instantiation with the common initializer remains an assembly obligation.

Consumer: the positive-reference weighted matrix comparison in `FamilyInputs`,
for `app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`,
and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol

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

/-- Finite-order positive-reference comparison on the supplied retained
leading charts, including the genuine conic inverse and both literal Jacobian
factors. The sole small difference premise is the immersion difference of
order `max 8 (m + 6)`. The original prescribed scalar domain and selected minor
are unchanged. Conic geometry must be supplied on these same maps by the
common-domain construction. Source: `app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_conic_primitives_sub_tolerance
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hKFU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hx : MapsTo Prod.fst K (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (D : CoefficientNormCharts n)
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.carrier K)
    (hSflow : MapsTo (densityCoordinates T) D.field.carrier
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
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) D.field.carrier
      (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)))
    (hDV : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    {Ki W Bi : Set (InputVariables n)} {Q Ωi : Set (Variables n × Euclidean 2)}
    (hKi : IsCompact Ki) (hconv : Convex ℝ Ki) (hW : IsOpen W) (hKiW : Ki ⊆ W)
    (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hQ : IsCompact Q) (hΩi : IsOpen Ωi) (hQΩi : Q ⊆ Ωi)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (hu₀ : ContDiffOn ℝ ∞ u₀ Ωi)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (slice : TransportSliceCoordinates n)
    (hrange₀ : MapsTo (inverseCoordinates u₀) Q Ki)
    (heq₀ : ∀ p ∈ Ωi, transportAveragedGradient (transportPosition T c₀.Q)
      (inverseCoordinates u₀ p) = p.1.2.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hgap₀ : ∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) D.field.carrier
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      ContDiffOn ℝ ∞ u Ωi → MapsTo (inverseCoordinates u) Q Ki →
      (∀ p ∈ Ωi, transportAveragedGradient (transportPosition T c.Q)
        (inverseCoordinates u p) = p.1.2.2) →
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T c.Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian slice (transportPosition T c.Q) p) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (m + 6)) (F - F₀) < δ →
      cNorm D.field.carrier (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) +
        cNorm D.field.carrier m (c.normal initial - c₀.normal initial) +
        cNorm D.field.carrier m (c.reduced - c₀.reduced) +
        cNorm D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) +
        cNorm Ki m (augmentedTransportGradient (transportPosition T c.Q) -
          augmentedTransportGradient (transportPosition T c₀.Q)) +
        cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) +
        cNorm Ki m (transportAbsoluteJacobian slice (transportPosition T c.Q) -
          transportAbsoluteJacobian slice (transportPosition T c₀.Q)) +
        cNorm Ki m ((fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c.Q) p)⁻¹) -
          (fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)⁻¹)) < ε := by
  have hD : IsCompact D.field.carrier := isCompact_closedBall _ _
  have hY₀ := (transportPosition_smooth T c₀.Q hP).mono hDV
  obtain ⟨C, hC, e, he, hgeom⟩ := exists_transportForwardJacobian_sub_le
    hKi hconv hW hKiW hBi hWBi hQ hΩi hQΩi D.field.isOpen_region hD
    D.field.ball_subset hIt hIIt hsegT hseg hY₀ hu₀ A slice hrange₀ heq₀
    (fun _ _ ↦ rfl) hgap hgap₀ m
  let tol := min e (ε / (1 + C))
  have htol : 0 < tol := lt_min he (div_pos hε (by positivity))
  obtain ⟨δ, hδ, hprimitive⟩ := RetainedLeading.exists_originalScalar_immersion_sub_tolerance
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx
    hD hSK hSflow c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀
    hR initial hi hipos hfoot₀ m htol
  refine ⟨δ, hδ, ?_⟩
  intro F c u hF him hrank hlow hmet hnormal hfoot hu hrange heq hdiffGap hJgap hsmall
  have hp := hprimitive F c hF him hrank hlow hmet hnormal hfoot hsmall
  let d := cNorm D.field.carrier (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q) +
    cNorm D.field.carrier m (c.normal initial - c₀.normal initial) +
    cNorm D.field.carrier m (c.reduced - c₀.reduced) +
    cNorm D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)
  change d < tol at hp
  have htransport : cNorm D.field.carrier (m + 2)
      (transportPosition T c.Q - transportPosition T c₀.Q) ≤ d := by
    dsimp only [d]
    linarith only [cNorm_nonneg D.field.carrier m (c.normal initial - c₀.normal initial),
      cNorm_nonneg D.field.carrier m (c.reduced - c₀.reduced),
      cNorm_nonneg D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse)]
  have hg := hgeom (transportPosition T c.Q) u
    (transportAbsoluteJacobian slice (transportPosition T c.Q)) d
    ((transportPosition_smooth T c.Q hP).mono hDV) hu hrange heq hdiffGap (fun _ _ ↦ rfl)
    hJgap htransport (hp.le.trans (min_le_left _ _))
  have hfinal : d * (1 + C) < ε :=
    (lt_div_iff₀ (show 0 < 1 + C by positivity)).mp (hp.trans_le (min_le_right _ _))
  change d + _ + _ + _ + _ < ε
  linarith only [hg, hfinal]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
