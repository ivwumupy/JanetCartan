module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicDensity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.CanonicalComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RescaledDensity

/-!
# Radially uniform weighted comparison on the retained positive family

The full original density class is retained while the fixed high-frequency
cutoff is dilated by an arbitrary factor at least one. The published
`NormalizedNormalLimit.RescaledDensity` estimate supplies frequency uniformity.
The physical, carrier and conic domains and all actual masks are unchanged.
Primitive differences are derived from closeness to the fixed positive
reference, before the varying density is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol
open WideDensity

/-- Fixed-reference finite norms control nearby primitive norms in the
retained shell comparison (`app:ch_background:prop:bg-frame`). -/
private theorem retained_shell_norm_le_reference_add_one {E H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set E} (hS : IsCompact S) {f f₀ : E → H} (m : ℕ)
    (hf : ∀ p ∈ S, ContDiffAt ℝ ∞ f p) (hf₀ : ∀ p ∈ S, ContDiffAt ℝ ∞ f₀ p)
    (hd : cNorm S m (f - f₀) ≤ 1) : cNorm S m f ≤ cNorm S m f₀ + 1 := by
  have h := cNorm_add_le_of_contDiffAt (r := m) hS
    (fun p hp ↦ ((hf p hp).sub (hf₀ p hp)).of_le (by simp))
    (fun p hp ↦ (hf₀ p hp).of_le (by simp))
  simp only [Pi.add_def, sub_add_cancel] at h
  change cNorm S m f ≤ cNorm S m (f - f₀) + cNorm S m f₀ at h
  linarith only [h, hd]

/-- Enlarge all coefficient budgets together without changing their charts
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
private theorem retained_shell_controls_enlarge
    {n N s : ℕ} {D : CoefficientNormCharts n} {a : Coefficients n N} {M M' : ℝ}
    (h : D.Controls s M (M + 1) 1 a) (hMM' : M ≤ M') :
    D.Controls s M' (M' + 1) 1 a := by
  have lift {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup H] [NormedSpace ℝ H]
      {d : PrimitiveNormChart E} {f : E → H}
      (hh : d.Controls s M (M + 1) 1 f) : d.Controls s M' (M' + 1) 1 f :=
    ⟨hh.smooth, hh.low.trans hMM', hh.high.trans (by nlinarith only [hMM'])⟩
  exact ⟨lift h.measurement, lift h.angular, lift h.high, lift h.normal, lift h.reduced⟩

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

/-- The actual retained positive family has a weighted matrix difference
uniform over ALL radial dilations of its fixed high-frequency cutoff. Both
original ODE labels and the original `R/8` density class are retained.
The immersion threshold precedes the varying immersion, density and radial
scale. Every coefficient, inverse, Jacobian and label difference is derived
from the existing retained immersion comparison. The published fixed-high
weighted estimate is applied without changing any detector support.

Consumer: `AmplitudeDifference.exists_fullAmplitude_sub_bounds_of_supported_shell`
for the fixed-reference SAME-row normal comparison. Sources:
`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_conic_weighted_shell_comparison
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
    (hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) D.field.region K)
    (hSflow : MapsTo (densityCoordinates T) D.field.region
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
    (hfoot₀ : MapsTo (densityFootpoint T c₀.inverse) D.field.region
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
    (hJ₀ : ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice (transportPosition T c₀.Q)) W)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ Ki, η ≤ ‖p.2.2‖)
    (hcontains : ∀ p ∈ Ki, D.Contains p)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hm : ContDiffOn ℝ ∞ (FixedCutoffs.physical hr 1) D.measurement.region)
    (ha : ContDiffOn ℝ ∞ (fun p ↦ angular p.1 p.2) D.angular.region)
    (hh : ContDiff ℝ ∞ high)
    (_hzero : ∀ r, r ≤ 1 → high r = 0) (hone : ∀ r, 2 ≤ r → high r = 1)
    (m : ℕ) (_hm1 : 1 ≤ m) :
    let L := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
    ∀ tol > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) D.field.region
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      ContDiffOn ℝ ∞ u Ωi → MapsTo (inverseCoordinates u) Q Ki →
      (∀ p ∈ Ωi, transportAveragedGradient (transportPosition T c.Q)
        (inverseCoordinates u p) = p.1.2.2) →
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T c.Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian slice (transportPosition T c.Q) p) →
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice (transportPosition T c.Q)) W →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (max 1 m + 6)) (F - F₀) < δ →
      ∀ d₀ : ℕ, m + 1 ≤ d₀ → ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      (∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) →
      ∀ t : ℝ, 1 ≤ t →
      let b := fun p ↦ inputDensity (rescaledCoefficients (TransportKernel.coefficientsOfCarrier
        (data T c.Q F row col c.forward c.inverse
          (fun y ↦ initial y * Real.sqrt (1 + v y)) hr hcell angular high)
        (FixedCutoffs.physical hr 1)) t)
        (transportAbsoluteJacobian slice (transportPosition T c.Q)) (inverseCoordinates u p)
      let b₀ := fun p ↦ inputDensity (rescaledCoefficients (TransportKernel.coefficientsOfCarrier
        (data T c₀.Q F₀ row col c₀.forward c₀.inverse
          (fun y ↦ initial y * Real.sqrt (1 + v y)) hr hcell angular high)
        (FixedCutoffs.physical hr 1)) t)
        (transportAbsoluteJacobian slice (transportPosition T c₀.Q)) (inverseCoordinates u₀ p)
      cNorm Q m (b - b₀) < tol := by
  dsimp only
  let L := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)
  let J₀ := transportAbsoluteJacobian slice (transportPosition T c₀.Q)
  let g₀ := fun side p ↦ densityFootpoint T c₀.inverse (densityEndpoint side (inverseCoordinates u₀ p))
  let a₀ := TransportKernel.coefficientsOfCarrier
    (data T c₀.Q F₀ row col c₀.forward c₀.inverse initial hr hcell angular high)
    (FixedCutoffs.physical hr 1)
  have hSKc := hSK.mono_left D.field.ball_subset
  have hSflowc := hSflow.mono_left D.field.ball_subset
  have hfoot₀c := hfoot₀.mono_left D.field.ball_subset
  have hend (side) : MapsTo (densityEndpoint side) Ki D.field.carrier := by
    intro p hp
    cases side
    · exact (hcontains p hp).2.2.2.2.1
    · exact (hcontains p hp).2.2.2.2.2
  have hfootSmooth {F : Euclidean n → Euclidean N}
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F) :
      ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) D.field.region := by
    intro p hp
    exact (c.densityFootpoint_spec.2.1.contDiffAt
      (((isOpen_Ioo.prod isOpen_ball).preimage (densityCoordinates T).continuous).mem_nhds
        ((outputCylinder_spec hRc hτ).2 (hSflow hp)))).contDiffWithinAt
  have hg₀ (side) (p) (hp : p ∈ Q) : ContDiffAt ℝ ∞ (g₀ side) p :=
    ((hfootSmooth c₀).contDiffAt (D.field.isOpen_region.mem_nhds
      (D.field.ball_subset (hend side (hrange₀ hp))))).comp
        (f := densityEndpoint side ∘ inverseCoordinates u₀) p
        ((densityEndpoint_contDiff side).contDiffAt.comp p
          ((inverseCoordinates_contDiffOn hu₀).contDiffAt (hΩi.mem_nhds (hQΩi hp))))
  have hball : ball ((0 : Euclidean (n - 1)), z₀) (R / 16) ⊆ L :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith only [hR]))
  have hgr₀ (side) : MapsTo (g₀ side) Q L :=
    fun p hp ↦ hball (hfoot₀c (hend side (hrange₀ hp)))
  obtain ⟨Mc, hMc, ha₀, δc, hδc, hcontrols⟩ :=
    exists_retained_originalScalar_coefficient_controls T hdomain hgeometry hP
      hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx D hSK hSflow c₀ hF₀ hi₀ hrank₀
      hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀ hr hcell angular high hm ha hh.contDiffOn m
  obtain ⟨Cg, hCg, hlabels⟩ := exists_retained_conic_footpoints_sub_le T D hRc hτ
    hSflowc c₀ hKi hQ hΩi hQΩi hend u₀ hu₀ hrange₀ m
  let Mw := Mc + cNorm Ki m J₀ + cNorm Q m (inverseCoordinates u₀) +
    cNorm Q m (g₀ false) + cNorm Q m (g₀ true) + 2
  have hMcMw : Mc ≤ Mw := by
    dsimp only [Mw]
    linarith only [cNorm_nonneg Ki m J₀, cNorm_nonneg Q m (inverseCoordinates u₀),
      cNorm_nonneg Q m (g₀ false), cNorm_nonneg Q m (g₀ true)]
  have hMw : 0 ≤ Mw := hMc.le.trans hMcMw
  have hJMw : cNorm Ki m J₀ + 1 ≤ Mw := by
    dsimp only [Mw]
    linarith only [hMc, cNorm_nonneg Q m (inverseCoordinates u₀),
      cNorm_nonneg Q m (g₀ false), cNorm_nonneg Q m (g₀ true)]
  have huMw : cNorm Q m (inverseCoordinates u₀) + 1 ≤ Mw := by
    dsimp only [Mw]
    linarith only [hMc, cNorm_nonneg Ki m J₀,
      cNorm_nonneg Q m (g₀ false), cNorm_nonneg Q m (g₀ true)]
  have hgMw (side) : cNorm Q m (g₀ side) + 1 ≤ Mw := by
    cases side <;> dsimp only [Mw] <;>
      linarith only [hMc, cNorm_nonneg Ki m J₀, cNorm_nonneg Q m (inverseCoordinates u₀),
        cNorm_nonneg Q m (g₀ false), cNorm_nonneg Q m (g₀ true)]
  obtain ⟨Cw, hCw, hweighted⟩ :=
    NormalizedNormalLimit.exists_rescaled_weighted_inputDensity_sub_le
    (N := N) D hh hone hKi hW hKiW hQ hΩi hQΩi (isCompact_closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (convex_closedBall _ _)
    hη hgap hfreq hcontains hJ₀ (fun p hp ↦ (hgap₀ p hp).trans (le_abs_self _)) m hMw
    (show cNorm Ki m J₀ ≤ Mw by linarith only [hJMw])
  intro tol htol
  let d := min 1 (min (1 / Cg) (tol / (2 * Cw * (1 + Cg))))
  have hd : 0 < d := lt_min zero_lt_one (lt_min (div_pos zero_lt_one hCg)
    (div_pos htol (by positivity)))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hgd1 : Cg * d ≤ 1 := by
    have hdg := (min_le_right 1 (min (1 / Cg) (tol / (2 * Cw * (1 + Cg))))).trans
      (min_le_left _ _)
    exact (mul_le_mul_of_nonneg_left hdg hCg.le).trans_eq (mul_div_cancel₀ _ hCg.ne')
  obtain ⟨δp, hδp, hprimitive⟩ := exists_retained_conic_primitives_sub_tolerance
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx D hSKc hSflowc
    c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀c
    hDV hKi hconv hW hKiW hBi hWBi hQ hΩi hQΩi hIt hIIt hsegT hseg u₀ hu₀ A slice
    hrange₀ heq₀ hgap hgap₀ m hd
  refine ⟨min δc δp, lt_min hδc hδp, ?_⟩
  intro F c u hF him hrank hlow hmet hnormal hfoot hu hrange heq hdiffGap hJgap hJ hsmall
    d₀ horder v hv hvm hpos t ht
  let b := fun p ↦ inputDensity (rescaledCoefficients (TransportKernel.coefficientsOfCarrier
    (data T c.Q F row col c.forward c.inverse
      (fun y ↦ initial y * Real.sqrt (1 + v y)) hr hcell angular high)
    (FixedCutoffs.physical hr 1)) t)
    (transportAbsoluteJacobian slice (transportPosition T c.Q)) (inverseCoordinates u p)
  let b₀ := fun p ↦ inputDensity (rescaledCoefficients (TransportKernel.coefficientsOfCarrier
    (data T c₀.Q F₀ row col c₀.forward c₀.inverse
      (fun y ↦ initial y * Real.sqrt (1 + v y)) hr hcell angular high)
    (FixedCutoffs.physical hr 1)) t)
    (transportAbsoluteJacobian slice (transportPosition T c₀.Q)) (inverseCoordinates u₀ p)
  let J := transportAbsoluteJacobian slice (transportPosition T c.Q)
  let g := fun side p ↦ densityFootpoint T c.inverse (densityEndpoint side (inverseCoordinates u p))
  let a := TransportKernel.coefficientsOfCarrier
    (data T c.Q F row col c.forward c.inverse initial hr hcell angular high)
    (FixedCutoffs.physical hr 1)
  have hsmallc := hsmall.trans_le (min_le_left _ _)
  have hsmallp : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
      (max 8 (m + 6)) (F - F₀) < δp :=
    (cNorm_mono_order (by omega : max 8 (m + 6) ≤ max 8 (max 1 m + 6))).trans_lt
      (hsmall.trans_le (min_le_right _ _))
  have hp := hprimitive F c u hF him hrank hlow hmet hnormal
    (hfoot.mono_left D.field.ball_subset) hu hrange heq hdiffGap hJgap hsmallp
  have hparts : cNorm D.field.carrier m (c.normal initial - c₀.normal initial) ≤ d ∧
      cNorm D.field.carrier m (c.reduced - c₀.reduced) ≤ d ∧
      cNorm D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse) ≤ d ∧
      cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) ≤ d ∧
      cNorm Ki m (J - J₀) ≤ d := by
    dsimp only [J, J₀]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hp,
        cNorm_nonneg D.field.carrier (m + 2) (transportPosition T c.Q - transportPosition T c₀.Q),
        cNorm_nonneg D.field.carrier m (c.normal initial - c₀.normal initial),
        cNorm_nonneg D.field.carrier m (c.reduced - c₀.reduced),
        cNorm_nonneg D.field.carrier m (densityFootpoint T c.inverse - densityFootpoint T c₀.inverse),
        cNorm_nonneg Ki m (augmentedTransportGradient (transportPosition T c.Q) -
          augmentedTransportGradient (transportPosition T c₀.Q)),
        cNorm_nonneg Q m (inverseCoordinates u - inverseCoordinates u₀),
        cNorm_nonneg Ki m (transportAbsoluteJacobian slice (transportPosition T c.Q) -
          transportAbsoluteJacobian slice (transportPosition T c₀.Q)),
        cNorm_nonneg Ki m ((fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c.Q) p)⁻¹) -
          (fun p ↦ (transportAbsoluteJacobian slice (transportPosition T c₀.Q) p)⁻¹))]
  have hl := hlabels F c u d hd.le hd1 hu hrange hparts.2.2.1 hparts.2.2.2.1
  have hJM : cNorm Ki m J ≤ Mw :=
    (retained_shell_norm_le_reference_add_one hKi m
      (fun p hp ↦ hJ.contDiffAt (hW.mem_nhds (hKiW hp)))
      (fun p hp ↦ hJ₀.contDiffAt (hW.mem_nhds (hKiW hp)))
      (hparts.2.2.2.2.trans hd1)).trans hJMw
  have huM : cNorm Q m (inverseCoordinates u) ≤ Mw :=
    (retained_shell_norm_le_reference_add_one hQ m
      (fun p hp ↦ (inverseCoordinates_contDiffOn hu).contDiffAt (hΩi.mem_nhds (hQΩi hp)))
      (fun p hp ↦ (inverseCoordinates_contDiffOn hu₀).contDiffAt (hΩi.mem_nhds (hQΩi hp)))
      (hparts.2.2.2.1.trans hd1)).trans huMw
  have hgM (side) : cNorm Q m (g side) ≤ Mw :=
    (retained_shell_norm_le_reference_add_one hQ m
      (fun p hp ↦ (hl.1 side p hp).1) (hg₀ side) ((hl.2 side).trans hgd1)).trans (hgMw side)
  let e := (1 + Cg) * d
  have hde : d ≤ e := by dsimp only [e]; nlinarith only [hd, hCg]
  have hge : Cg * d ≤ e := by dsimp only [e]; nlinarith only [hd]
  have hadiff :
      cNorm D.measurement.carrier m (a.measurement - a₀.measurement) ≤ e ∧
      cNorm D.angular.carrier m (a.angular - a₀.angular) ≤ e ∧
      cNorm D.high.carrier m (a.high - a₀.high) ≤ e ∧
      cNorm D.field.carrier m (a.normal - a₀.normal) ≤ e ∧
      cNorm D.field.carrier m (a.reduced - a₀.reduced) ≤ e := by
    dsimp only [a, a₀]
    rw [c.coefficients_eq, c₀.coefficients_eq]
    refine ⟨?_, ?_, ?_, hparts.1.trans hde, hparts.2.1.trans hde⟩ <;>
      simpa only [sub_self, cNorm_zero] using hd.le.trans hde
  have hgr (side) : MapsTo (g side) Q L :=
    fun p hp ↦ hball (hfoot (D.field.ball_subset (hend side (hrange hp))))
  have hw := hweighted a a₀ J u u₀ g g₀ e (hd.le.trans hde) rfl rfl
    (retained_shell_controls_enlarge (hcontrols F c hF him hrank hlow hmet hnormal hfoot hsmallc) hMcMw)
    (retained_shell_controls_enlarge ha₀ hMcMw)
    hJ (fun p hp ↦ (hJgap p hp).trans (le_abs_self _)) hJM hu hu₀ hrange hrange₀
    huM (by linarith only [huMw]) (fun side p hp ↦ (hl.1 side p hp).1) hg₀ hgr hgr₀ hgM
    (fun side ↦ by linarith only [hgMw side])
    hadiff.1 hadiff.2.1 hadiff.2.2.2.1 hadiff.2.2.2.2
    (hparts.2.2.2.2.trans hde) (hparts.2.2.2.1.trans hde)
    (fun side ↦ (hl.2 side).trans hge) d₀ horder v hv hvm t ht
  let bw := fun p ↦ densityPair v g p •
    inputDensity (rescaledCoefficients a t) J (inverseCoordinates u p)
  let bw₀ := fun p ↦ densityPair v g₀ p •
    inputDensity (rescaledCoefficients a₀ t) J₀ (inverseCoordinates u₀ p)
  have heq (p) (hp : p ∈ Q) : b =ᶠ[𝓝 p] bw :=
    canonical_substitutedDensity_initial_mul_sqrtDensity_eventuallyEq
      T c.Q F row col c.forward c.inverse hr hcell angular (fun r ↦ high (t * r)) initial v J u p
      (fun side ↦ (hl.1 side p hp).1.continuousAt)
      (fun side ↦ (hv _ (hgr side hp)).continuousAt)
      (fun side ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos _ (hgr side hp)))
  have heq₀' (p) (hp : p ∈ Q) : b₀ =ᶠ[𝓝 p] bw₀ :=
    canonical_substitutedDensity_initial_mul_sqrtDensity_eventuallyEq
      T c₀.Q F₀ row col c₀.forward c₀.inverse hr hcell angular (fun r ↦ high (t * r)) initial v J₀ u₀ p
      (fun side ↦ (hg₀ side p hp).continuousAt)
      (fun side ↦ (hv _ (hgr₀ side hp)).continuousAt)
      (fun side ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos _ (hgr₀ side hp)))
  have hsub : cNorm Q m (b - b₀) = cNorm Q m (bw - bw₀) :=
    GeometricProfile.cNorm_eq_of_eventuallyEq
      (fun p hp ↦ (heq p hp).sub (heq₀' p hp)) m
  have hfinal : Cw * e < tol := by
    have hdlast : d ≤ tol / (2 * Cw * (1 + Cg)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * Cw * (1 + Cg))).mp hdlast
    dsimp only [e]
    nlinarith only [hh, htol]
  exact hsub.trans_le hw.2.2 |>.trans_lt hfinal

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
