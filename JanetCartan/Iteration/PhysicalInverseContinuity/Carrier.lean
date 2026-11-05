module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Columns
public import JanetCartan.Iteration.PhysicalInverseContinuity.Tail

/-!
# Strong uncut adjoint continuity for the actual original retained carrier

The finite immersion-jet neighborhood is chosen after the fixed raw budget,
datum and tolerance, but before the current chart or its realization. The
original-scalar Hamilton/ODE comparison produces all finite-frequency kernel
differences. The actual order-one raw adjoint estimates give both uncut tails.
No whole-row operator-norm continuity or changed source is used. Consumer:
the strong adjoint remainder in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.PhysicalInverseContinuity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CarrierSobolev
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction.TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {z₀ : Euclidean 3} {Rc B τ : ℝ} {row col : Fin n}

/-- At a fixed datum and common order-one raw budget, an order-eight physical
jet neighborhood gives the prescribed strong adjoint tolerance on the same
realized *uncut* carrier. The two raw budgets are exactly the carrier-slot
consequences of the actual augmented adjoint Sobolev estimates. -/
theorem exists_retained_uncut_adjoint_sub_tolerance
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
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hKΩK : IsCompact K) (hKΩ : K ⊆ Ω)
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
    (hSphase : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
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
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hangular : ∀ z η, |angular z η| ≤ 1) (hang : ContDiff ℝ ∞ (Function.uncurry angular))
    {Z : Set CarrierParameter} (hZ : IsCompact Z) (hzero : ∀ z ∉ Z, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical hr 1) ×ˢ Z ⊆ D.field.carrier)
    (V₀ : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hV₀ : ∀ v, V₀.adjoint v =ᵐ[carrierMeasure n] carrierAdjointIntegral
      (data T c₀.Q F₀ row col c₀.forward c₀.inverse initial hr hcell angular FixedCutoffs.highFrequency) v)
    (w : ComplexOutputL2 n) (hraw₀ : MemRawSobolev 1 (V₀.adjoint w))
    {Craw : ℝ} (hCraw : 0 ≤ Craw) (hbound₀ : rawSobolevNorm 1 (V₀.adjoint w) ≤ Craw)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      MapsTo (densityFootpoint T c.inverse) D.field.region
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 8 (F - F₀) < δ →
      ∀ (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ v, V.adjoint v =ᵐ[carrierMeasure n] carrierAdjointIntegral
        (data T c.Q F row col c.forward c.inverse initial hr hcell angular FixedCutoffs.highFrequency) v) →
      MemRawSobolev 1 (V.adjoint w) → rawSobolevNorm 1 (V.adjoint w) ≤ Craw →
      ‖V.adjoint w - V₀.adjoint w‖ ≤ ε := by
  let Kcut := 1 + 4 * Craw / ε
  have hK : 1 ≤ Kcut := by
    dsimp [Kcut]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCraw) hε.le]
  have hKpos : 0 < Kcut := zero_lt_one.trans_le hK
  have htail : (Kcut ^ 1)⁻¹ * (Craw + Craw) ≤ ε / 2 := by
    rw [pow_one, inv_mul_eq_div, div_le_iff₀ hKpos]
    have he : ε * Kcut = ε + 4 * Craw := by
      dsimp [Kcut]
      field_simp
    nlinarith only [he, hε.le]
  let Bbox := ‖w‖ * carrierBoxFactor (n := n) Z Kcut
  have hBbox : 0 ≤ Bbox := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  let η := ε / (2 * (1 + Bbox))
  have hη : 0 < η := div_pos hε (by positivity)
  have hcompact : (η * ‖w‖) * carrierBoxFactor (n := n) Z Kcut ≤ ε / 2 := by
    have he : η * (2 * (1 + Bbox)) = ε := div_mul_cancel₀ _ (by positivity)
    calc
      _ = η * Bbox := by dsimp [Bbox]; ring
      _ ≤ ε / 2 := by nlinarith only [he, hη.le]
  have hhigh (ρ : ℝ) : |FixedCutoffs.highFrequency ρ| ≤ 1 := by
    rw [abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc ρ).1]
    exact (FixedCutoffs.highFrequency_mem_Icc ρ).2
  obtain ⟨δ, hδ, hk⟩ := exists_retained_carrierKernel_sub_tolerance T hdomain hgeometry hP
    hΩ hKΩK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx D hSK hSflow hSphase
    c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀
    hr hcell angular FixedCutoffs.highFrequency hangular hhigh hzero hsupport
    (by positivity : 0 ≤ 4 * Kcut) hη
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hsmall V hV hraw hbound
  have hcol := memLp_retained_carrierKernel_column T c hP hRc hτ hKΩ hKU hF him hrank
    D hSK hSflow hSphase hR initial hi hipos hfoot hr hcell angular hang hZ hzero hsupport
  have hcol₀ := memLp_retained_carrierKernel_column T c₀ hP hRc hτ hKΩ hKU hF₀ hi₀ hrank₀
    D hSK hSflow hSphase hR initial hi hipos hfoot₀ hr hcell angular hang hZ hzero hsupport
  have h := norm_carrier_adjoint_sub_le_of_primitive_kernel _ _ V V₀ hV hV₀ hcol hcol₀
    hZ hzero hzero hK hη.le (hk F c hF him hrank hlow hmet hnormal hfoot hsmall) w 1 hraw hraw₀
  calc
    _ ≤ _ := h
    _ ≤ (Kcut ^ 1)⁻¹ * (Craw + Craw) + (η * ‖w‖) * carrierBoxFactor (n := n) Z Kcut :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hbound hbound₀) (by positivity)) le_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add htail hcompact
    _ = ε := add_halves ε

end JanetCartan.PhysicalInverseContinuity
