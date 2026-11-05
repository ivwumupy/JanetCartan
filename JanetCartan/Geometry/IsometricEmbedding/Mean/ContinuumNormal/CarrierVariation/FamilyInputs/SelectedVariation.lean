module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedSpectralAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SelectedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.OperatorDifference.RetainedCell
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.StressPrimitives

/-!
# Positive-reference variation on already selected conic geometry

The existing selected geometry is applied to the reference and varying frames.
Immersion closeness proves admission, and the original forward-flow estimate
proves the label range on the full supplied coefficient chart. No new incidence
mask, conic inverse, scalar domain or auxiliary slice witness is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CanonicalConic PositiveReference PositiveReference.FlowConstruction
open HamiltonPhase ProjectedStressFrame ContinuumNormalReduction TransportSymbol
open FullPhaseCharts ActualComparison WideDensity RetainedRowGeometry CarrierNormalRealization
open Pseudodifferential AmplitudeBound
open ContinuumAdjoint.Canonical.RetainedCellAdjoint

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

/-- Apply the full-amplitude comparison to the actual selected geometry.
The geometric callback is the current-branch projection of
`NormalizedSelection.exists_finite_incidence_comparison_inputs`. Immersion
closeness supplies current admission; both ODE-label ranges follow from the
original output cylinder, time cap and forward C¹ estimate. Independent
spectral witnesses are handled separately. All masks, outer domains, the
original density ball and reflected factor four are retained. The literal
real-normal difference retains every supplied operator with the same dense
test action; the forward/adjoint output is the original retained constructor's
output, rather than an independently identified existential witness.

Consumer: `ActualConstruction.norm_physicalNormal_sub_le_image_and_full_amplitudes`
and retained-history normal variation. Sources:
`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-Psi`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_fullAmplitude_comparison_on_selected_geometry
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ) (hτRc : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hKFU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hx : MapsTo Prod.fst K (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rOuter aOuter : ℝ}
    (hηb : ηb ≠ 0) (hrOuter : 0 < rOuter)
    (D : CoefficientNormCharts n)
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
    {Mc : ℝ} (hMc : 0 < Mc)
    (hforward₀ : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 c₀.forward ≤ Mc)
    (hlabels : ∀ p ∈ D.field.region, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64))
    (htime : ∀ p ∈ D.field.region, |(densityCoordinates T p).1| < R / (64 * Mc))
    (hDV : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    {Ki W Bi : Set (InputVariables n)} {Q Ωi : Set (Variables n × Euclidean 2)}
    (hKi : IsCompact Ki) (hconv : Convex ℝ Ki) (hW : IsOpen W) (hKiW : Ki ⊆ W)
    (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hQ : IsCompact Q) (hΩi : IsOpen Ωi) (hQΩi : Q ⊆ Ωi)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {gap : ℝ} (hgap : 0 < gap)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ Ki, η ≤ ‖p.2.2‖)
    (hcontains : ∀ p ∈ Ki, D.Contains p)
    (hWDom : W ⊆ symbolInputDomain zRoot ηb rOuter (6 * aOuter))
    {r rAngular : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hrAngular : 0 < rAngular) (hrr : rAngular ≤ rOuter)
    (haa : r ≤ aOuter) (har : r ≤ rAngular)
    (hQradius : ∀ p ∈ Q, ‖p.1.2.2‖ = 1 / 4)
    (hne : ∀ p ∈ Ωi, p.1.2.2 ≠ 0)
    (hscale : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ωi ↔ p ∈ Ωi)
    {δgeometry : ℝ}
    (hframe₀ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F₀ - fun _ ↦ cubeStress n) < δgeometry)
    (hselected : ∀ (F : Euclidean n → Euclidean N)
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry →
      let QF : {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (QF - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedFrozen.RetainedSpectralGeometry T QF zRoot ηb rOuter aOuter ∧
      Ωi ⊆ symbolDomain T QF zRoot ηb rOuter (6 * aOuter) ∧
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse T QF zRoot ηb rOuter (6 * aOuter))
        (normalizeOutputRadius (1 / 4) q)) Ωi Ki ∧
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T QF) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb rAngular r,
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T QF) p) ∈ Q))
    (m : ℕ) (hreserve : 2 * (n + 1) ≤ m) :
    ∀ tol > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
        1 c.forward ≤ Mc →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (max 1 m + 6)) (F - F₀) < δ →
      ∀ d₀ : ℕ, m + 1 ≤ d₀ → ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) d₀ v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let angular := angularMask zRoot (NormedSpace.normalize ηb) hr (angularWidth_spec hηb hrAngular).1
      let d := TransportKernel.coefficientsOfCarrier
        (data T c.Q F row col c.forward c.inverse (fun y ↦ initial y * Real.sqrt (1 + v y))
          hr hcell angular FixedCutoffs.highFrequency) (FixedCutoffs.physical hr 1)
      let dref := TransportKernel.coefficientsOfCarrier
        (data T c₀.Q F₀ row col c₀.forward c₀.inverse (fun y ↦ initial y * Real.sqrt (1 + v y))
          hr hcell angular FixedCutoffs.highFrequency) (FixedCutoffs.physical hr 1)
      let u := symbolInverse T c.Q zRoot ηb rOuter (6 * aOuter)
      let uref := symbolInverse T c₀.Q zRoot ηb rOuter (6 * aOuter)
      let S := closedBall (spectatorCenter zRoot) (r / 2)
      (∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude d (symbolJacobian T c.Q) u
          (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j -
          fullComplexMatrixAmplitude dref (symbolJacobian T c₀.Q) uref
          (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j) m tol ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude d (symbolJacobian T c.Q) u
          (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j -
          fullReflectedMatrixAmplitude dref (symbolJacobian T c₀.Q) uref
          (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j) m (4 * tol)) ∧
      let f := fun t : Bool ↦ if t then F else F₀
      let q := fun t : Bool ↦ if t then c.Q else c₀.Q
      let φ := fun t : Bool ↦ if t then c.forward else c₀.forward
      let y := fun t : Bool ↦ if t then c.inverse else c₀.inverse
      let weighted := fun p ↦ initial p * Real.sqrt (1 + v p)
      let e := fun t ↦ data T (q t) (f t) row col (φ t) (y t) weighted
        hr hcell angular FixedCutoffs.highFrequency
      ∀ (χ : C(Torus n, ℝ)), ‖χ‖ ≤ 1 →
      ∀ (KF : Set (Euclidean n)) (Cnormal Cpdo Cmask H : Bool → ℝ)
        (Cbound : Bool → ℕ → ℝ)
        (Uop : Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ t, RetainedCellForwardAdjointOutput (K := KF)
        (Kinitial := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
        T (q t) (f t) row col (φ t) (y t) weighted zRoot ηb rOuter aOuter rAngular r hr hrAngular hηb
        (Cnormal t) (Cpdo t) (Cmask t) (H t) m hreserve (e t)
        (TransportKernel.coefficientsOfCarrier (e t) (FixedCutoffs.physical hr 1)) (Cbound t)) →
      (∀ t w, Uop t (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e t) w.val) →
      ‖carrierChannel (CommonMeasurement.restrictCarrier χ (Uop true)) ∘L
          (carrierChannel (CommonMeasurement.restrictCarrier χ (Uop true))).adjoint -
        carrierChannel (CommonMeasurement.restrictCarrier χ (Uop false)) ∘L
          (carrierChannel (CommonMeasurement.restrictCarrier χ (Uop false))).adjoint‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * r) * (4 * tol)) := by
  have hflow (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F) :
      MapsTo (densityCoordinates T) D.field.region c.D :=
    hSflow.mono_right ((outputCylinder_spec hRc hτ).2.trans c.small_subset)
  have hSK : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      D.field.region K := by
    intro p hp
    have hbig := c₀.subset_big (hflow F₀ c₀ hp)
    have hcoords : densityCoordinates T p ∈
        closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc := by
      rw [← closedBall_prod_same]
      refine ⟨?_, ball_subset_closedBall ((ball_subset_ball (by linarith : Rc / 4 ≤ Rc)) hbig.2)⟩
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      constructor <;> linarith [hbig.1.1, hbig.1.2]
    have hm := hbuffer hcoords
    change (coordinates (adaptedCoordinates T.data.adapted)).symm
      (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ K at hm
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm
  have hfoot (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (hforward : cNorm (Icc (-τ) τ ×ˢ
        closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 c.forward ≤ Mc) :
      MapsTo (densityFootpoint T c.inverse) D.field.region
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) := by
    intro p hp
    have hdist := ContinuumAdjoint.Canonical.RetainedLeading.inverseFootpoint_dist_le_of_forward_cNorm
      z₀ hRc hτ c.forward c.inverse c.D c.inverse_range c.initial c.forward_inverse
      c.forward_buffer_smooth hforward (hflow F c hp)
    have hstep : Mc * |(densityCoordinates T p).1| < R / 64 := by
      have hh := mul_lt_mul_of_pos_left (htime p hp) hMc
      have heq : Mc * (R / (64 * Mc)) = R / 64 := by field_simp
      rwa [heq] at hh
    have htri := dist_triangle (densityFootpoint T c.inverse p)
      (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), z₀)
    have hl := mem_closedBall.mp (hlabels p hp)
    change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), z₀) < R / 16
    change dist (c.inverse (densityCoordinates T p)) ((0 : Euclidean (n - 1)), z₀) ≤
      dist (c.inverse (densityCoordinates T p)) (densityCoordinates T p).2 +
        dist (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), z₀) at htri
    linarith
  have hselectedChart (F : Euclidean n → Euclidean N)
      (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U)
      (hframe : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry) := by
    have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
      simpa only [c.frame_eq] using c.Q.2.2
    have heq : (⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < T.family.threshold}) = c.Q :=
      Subtype.ext c.frame_eq.symm
    have hh := hselected F hF hi hrank hlow hframe
    dsimp only at hh
    rw [heq] at hh
    exact hh
  obtain ⟨hspectral₀, hdom₀, hnorm₀, _hdiff₀, hgap₀, hmask₀⟩ :=
    hselectedChart F₀ c₀ hF₀ hi₀ hrank₀ hframe₀
  obtain ⟨hbuffer₀, hshell₀⟩ := NormalizedNormalLimit.transport_mask_closure_geometry_of_normalized_image
    (by norm_num : (0 : ℝ) < 1 / 4) hQ hQΩi hscale hmask₀
  intro tol htol
  obtain ⟨δa, hδa, hfull⟩ := exists_retained_conic_fullAmplitude_comparison_of_spectral_geometry
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx
    hηb hrOuter D hSK hSflow c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀
    hR initial hi hipos (hfoot F₀ c₀ hforward₀) hDV hKi hconv hW hKiW hBi hWBi
    hQ hΩi hQΩi hIt hIIt hsegT hseg A hgap hgap₀ hη hfreq hcontains hWDom
    hr hcell hrAngular hrr haa har hQradius hne hscale hspectral₀ hdom₀ hnorm₀
    hbuffer₀ (fun p hp v _ hv ↦ hshell₀ (p, v) hv hp) m hreserve tol htol
  obtain ⟨δf, hδf, hadmit⟩ := exists_admissible_projectedStress_sub_tolerance
    (isCompact_closedBall _ _) hU hKFU hF₀ hi₀ hrank₀ hκmet hκnormal
    hlow₀ hmet₀ hnormal₀ hframe₀ 6 (by norm_num : (0 : ℝ) < 1)
  refine ⟨min δa δf, lt_min hδa hδf, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hforward hsmall
  have hframe := (hadmit F hF him hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 8 (6 + 2) ≤ max 8 (max 1 m + 6))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))).1
  obtain ⟨hspectral, hdom, hnorm, hdiff, hJgap, hmask⟩ :=
    hselectedChart F c hF him hrank hframe
  obtain ⟨hbufferCurrent, hshellCurrent⟩ := NormalizedNormalLimit.transport_mask_closure_geometry_of_normalized_image
    (by norm_num : (0 : ℝ) < 1 / 4) hQ hQΩi hscale hmask
  have hmatrix := hfull F c hF him hrank hlow hmet hnormal (hfoot F c hforward) hspectral
    hdom hnorm hdiff hJgap hbufferCurrent (fun p hp v _ hv ↦ hshellCurrent (p, v) hv hp)
    (hsmall.trans_le (min_le_left _ _))
  intro d₀ horder v hv hvm hpos angular d dref u uref S
  have hdifference := hmatrix d₀ horder v hv hvm hpos
  refine ⟨hdifference, ?_⟩
  intro f q φ y weighted e χ hχ KF Cnormal Cpdo Cmask H Cbound Uop houtput hUop
  exact retainedCell_realNormal_sub_norm_le_fullAmplitude T q f row col φ y weighted
    (K := KF) (Kinitial := closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8))
    zRoot ηb rOuter aOuter rAngular r hr hrAngular hcell hηb Cnormal Cpdo Cmask H Cbound
    m hreserve Uop χ hχ tol houtput hUop (fun i j ↦ (hdifference i j).2)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
