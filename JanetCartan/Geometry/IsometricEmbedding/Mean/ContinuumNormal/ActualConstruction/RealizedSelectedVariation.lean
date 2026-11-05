module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.RetainedDensityNormals
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SelectedVariation

/-!
# Realized normal comparison on the supplied retained geometry

The published selected full-amplitude comparison gives one map tolerance before
all original densities. Apply the primitive carrier construction on each of the
two supplied charts, with its own valid amplitude witnesses, and then compare
the literal normals. No forward/adjoint-output record is assumed.

The geometric callback is the current projection of the original joint
incidence geometry. It is used unchanged for both the realization and the
comparison; all parameter, density and measurement domains remain fixed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection NormalizedCarrierProfiles
open CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase RetainedRowGeometry
open NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 RetainedFrozen
open LeadingWave LeadingWave.JointReconstruction AmbientResponse GeometricProfile
open ProjectedStressFrame WideDensity

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

/-- Construct both retained density carriers and their literal adjoints, then
apply the actual full-amplitude variation to their measured normals. The map
tolerance precedes the original `2*(n+1)+14` density class. Test uniqueness
allows an existing reference carrier to be retained. The geometric callback is
supplied by `NormalizedSelection.exists_finite_incidence_comparison_inputs`;
its original-family application is still required. Consumer: finite-history
coercivity (`app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_background:eq:bg-T`). -/
theorem exists_realized_retained_density_normal_comparison
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
    {σ : ℝ} (hσ : 0 < σ)
    {Mc : ℝ} (hMc : 0 < Mc)
    (hforward₀ : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 c₀.forward ≤ Mc)
    (hlabels : ∀ p ∈ D.field.region, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64))
    (htime : ∀ p ∈ D.field.region, |(densityCoordinates T p).1| < R / (64 * Mc))
    (hDV : D.field.region ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρi τi : ℝ} (hρi : 0 < ρi) (hτi : 0 < τi)
    {W Bi : Set (InputVariables n)} {Q Ωi : Set (Variables n × Euclidean 2)}
    (hW : IsOpen W) (hKiW : closedBall p₀ ρi ⊆ W)
    (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hQ : IsCompact Q) (hΩi : IsOpen Ωi) (hQΩi : Q ⊆ Ωi)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {gap : ℝ} (hgap : 0 < gap)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ Bi, η ≤ ‖p.2.2‖)
    (hcontains : ∀ p ∈ (closedBall p₀ ρi), D.Contains p)
    (hBiDom : Bi ⊆ symbolInputDomain zRoot ηb rOuter (6 * aOuter))
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
        (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρi) ∧
      (∀ p ∈ (closedBall p₀ ρi), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T QF)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T QF) p) ∧
      (∀ p ∈ conicMaskSupport zRoot ηb rAngular r,
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T QF) p) ∈ Q) ∧
      closedBall q₀ (2 * τi) ⊆ symbolDomain T QF zRoot ηb rOuter (6 * aOuter) ∧
      MapsTo (inverseCoordinates (symbolInverse T QF zRoot ηb rOuter (6 * aOuter)))
        (closedBall q₀ (2 * τi)) (closedBall p₀ ρi) ∧
      (closure (augmentedTransportGradient (transportPosition T QF) ''
        conicMaskSupport zRoot ηb rAngular r) ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain T QF zRoot ηb rOuter (6 * aOuter)) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T QF) ''
          conicMaskSupport zRoot ηb rAngular r) → (x, v) ∈ closedBall q₀ τi) ∧
      (∀ p ∈ symbolDomain T QF zRoot ηb rOuter (6 * aOuter),
        ‖(symbolInverse T QF zRoot ηb rOuter (6 * aOuter) p).2‖ ≤ 2 * ‖p.1.2.2‖))
    {Rphysical : ℝ} {V : Set CarrierParameter}
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hRT : Rphysical ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) Rphysical ⊆ U)
    (hRtime : Rphysical ≤ R / (64 * Mc))
    (hD : D.field.region ⊆ ball (0 : Euclidean n) Rphysical ×ˢ V)
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) Rphysical ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ))
    (hlabelProduct : ∀ p ∈ ball (0 : Euclidean n) Rphysical ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 64))
    (haR : 6 * aOuter < T.family.radius)
    (houter : coefficientDomain zRoot rOuter (6 * aOuter) ⊆ ball (0 : Euclidean n) Rphysical ×ˢ V)
    (hDouter : D.field.region ⊆ coefficientDomain zRoot rOuter (6 * aOuter))
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ
      carrierSupport zRoot (r := r) ⊆ D.field.carrier) :
    ∀ tol > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N)
      (current : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 4 F ≤ M →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
        ∀ w ∈ normalSpace F x, κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
        1 current.forward ≤ Mc →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
        (max 8 (max 1 (2 * (n + 1)) + 6)) (F - F₀) < δ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 4), 0 < 1 + v p) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (2 * (n + 1) + 14) v ≤ 1 →
      (∀ p ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8), (1 / 2 : ℝ) ≤ 1 + v p) →
      let f := fun t : Bool ↦ if t then F else F₀
      let cp : ∀ t, Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col (f t) :=
        fun t ↦ Bool.rec c₀ current t
      let angular := angularMask zRoot (NormedSpace.normalize ηb) hr (angularWidth_spec hηb hrAngular).1
      let e := fun t ↦ data T (cp t).Q (f t) row col (cp t).forward (cp t).inverse
        (fun p ↦ positiveDensityAmplitude σ (v p)) hr hcell angular FixedCutoffs.highFrequency
      ∃ Uop : Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ t w, Uop t (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e t) w.val) ∧
        (∀ t (w : ComplexOutputL2 n), MemLp (carrierAdjointIntegral (e t) w) 2 (carrierMeasure n) ∧
          (Uop t).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e t) w) ∧
        (∀ t w, ∀ᵐ x ∂volume, x ∉ (e t).outputChart → Uop t w x = 0) ∧
        (∀ Wop : Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ t w, Wop t (carrierInitialTestToLp w) =ᵐ[volume] carrierTestIntegral (e t) w.val) →
          Wop = Uop) ∧
        ∀ (χ : C(Torus n, ℝ)), ‖χ‖ ≤ 1 →
          ‖carrierChannel (CommonMeasurement.restrictCarrier χ (Uop true)) ∘L
              (carrierChannel (CommonMeasurement.restrictCarrier χ (Uop true))).adjoint -
            carrierChannel (CommonMeasurement.restrictCarrier χ (Uop false)) ∘L
              (carrierChannel (CommonMeasurement.restrictCarrier χ (Uop false))).adjoint‖ ≤
            (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * r) * (4 * tol)) := by
  classical
  have hselectedChart (F : Euclidean n → Euclidean N)
      (current : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F)
      (hF : ContDiffOn ℝ ∞ F U) (him : IsImmersionOn F U)
      (hrank : HasFullNormalRankOn F U)
      (hframe : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry) := by
    have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
      simpa only [current.frame_eq] using current.Q.2.2
    have heq : (⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF him hrank), hlow⟩ :
        {QF : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ QF U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < T.family.threshold}) = current.Q :=
      Subtype.ext current.frame_eq.symm
    have hh := hselected F hF him hrank hlow hframe
    dsimp only at hh
    rw [heq] at hh
    exact hh
  intro tol htol
  obtain ⟨δa, hδa, hcompare⟩ := exists_retained_fullAmplitude_comparison_on_selected_geometry
    T hdomain hgeometry hP hΩ hK hKΩ hRc hB hτ hτRc hbuffer hτeq hKFU hKU hx
    hηb hrOuter D hSflow c₀ hF₀ hi₀ hrank₀ hκmet hκnormal hlow₀ hmet₀ hnormal₀
    hR (fun _ ↦ σ) contDiffOn_const (fun _ _ ↦ hσ) hMc hforward₀ hlabels htime hDV
    (isCompact_closedBall _ _) (convex_closedBall _ _) hW hKiW hBi hWBi hQ hΩi hQΩi
    hIt hIIt hsegT hseg A hgap hη (fun p hp ↦ hfreq p (hWBi (hKiW hp)))
    hcontains (hWBi.trans hBiDom) hr hcell hrAngular hrr haa har hQradius hne hscale hframe₀
    (fun F hF him hrank hlow hframe ↦ by
      obtain ⟨hs, hd, hn, hdiff, hJac, hmask, _⟩ := hselected F hF him hrank hlow hframe
      exact ⟨hs, hd, hn, hdiff, fun p hp ↦ hJac p (hWBi (hKiW hp)), hmask⟩)
    (2 * (n + 1)) le_rfl tol htol
  obtain ⟨δf, hδf, hadmit⟩ := exists_admissible_projectedStress_sub_tolerance
    (isCompact_closedBall _ _) hU hKFU hF₀ hi₀ hrank₀ hκmet hκnormal
    hlow₀ hmet₀ hnormal₀ hframe₀ 6 (by norm_num : (0 : ℝ) < 1)
  refine ⟨min δa δf, lt_min hδa hδf, ?_⟩
  intro F current hF him hrank hlow hmet hnormal hforward hsmall v hv hvpos hvm hpos
    f cp angular e
  have hframe := (hadmit F hF him hrank hlow hmet hnormal
    ((cNorm_mono_order (by omega : max 8 (6 + 2) ≤ max 8 (max 1 (2 * (n + 1)) + 6))).trans_lt
      (hsmall.trans_le (min_le_right _ _)))).1
  have hFp (t : Bool) : ContDiffOn ℝ ∞ (f t) U := by
    cases t with
    | false => exact hF₀
    | true => exact hF
  have himp (t : Bool) : IsImmersionOn (f t) U := by
    cases t with
    | false => exact hi₀
    | true => exact him
  have hrankp (t : Bool) : HasFullNormalRankOn (f t) U := by
    cases t with
    | false => exact hrank₀
    | true => exact hrank
  have hframep (t : Bool) : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress (f t) - fun _ ↦ cubeStress n) < δgeometry := by
    cases t with
    | false => exact hframe₀
    | true => exact hframe
  have hforwardp (t : Bool) : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) 1 (cp t).forward ≤ Mc := by
    cases t with
    | false => exact hforward₀
    | true => exact hforward
  have hrealize (t : Bool) := by
    obtain ⟨hs, _hd, _hn, hdiff, hJac, _hmask, hout, hrange, hpunct, hshell, hupper⟩ :=
      hselectedChart (f t) (cp t) (hFp t) (himp t) (hrankp t) (hframep t)
    exact exists_retained_chart_density_normal hP T (hFp t) (himp t) (hrankp t) (cp t)
      hRc hτ hR hMc (hforwardp t) hRT hRU hRtime hV hVP hflow hlabelProduct D hD zRoot hηb
      hrOuter hrAngular hr hrr haa har hcell haR houter hDouter hsupportD p₀ q₀ hρi hτi
      hW hKiW hBi hWBi hBiDom hcontains hIt hIIt hsegT hseg A hη hgap hfreq hs hout hrange
      hdiff hJac hpunct hshell hupper v hv hvpos (σ := σ)
  choose Cnorm hCnorm Cpdo hCpdo hsupp hb hA Uop hUnorm hUadj htest hsupported huniq hadj hUnormal
    using hrealize
  refine ⟨Uop, htest, hadj, hsupported, ?_, ?_⟩
  · intro Wop hWop
    funext t
    exact huniq t (Wop t) (hWop t)
  · intro χ hχ
    have hvat : ∀ p ∈ closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8),
        ContDiffAt ℝ ∞ v p := fun p hp ↦
      hv.contDiffAt (isOpen_ball.mem_nhds
        ((closedBall_subset_ball (by linarith : R / 8 < R / 4)) hp))
    have hfull := (hcompare F current hF him hrank hlow hmet hnormal hforward
      (hsmall.trans_le (min_le_left _ _)) (2 * (n + 1) + 14) (by omega) v hvat hvm hpos).1
    let d := fun t ↦ coefficientsOfCarrier (e t) (FixedCutoffs.physical hr 1)
    let J := fun t ↦ symbolJacobian T (cp t).Q
    let u := fun t ↦ symbolInverse T (cp t).Q zRoot ηb rOuter (6 * aOuter)
    let Ωs := fun t ↦ symbolDomain T (cp t).Q zRoot ηb rOuter (6 * aOuter)
    let S := closedBall (spectatorCenter zRoot) (r / 2)
    let b := fun t ↦ fullReflectedMatrixAmplitude (d t) (J t) (u t) (Ωs t) S
    have hs (t) := fullReflectedMatrixAmplitude_supportedInCenteredBox
      (d t) (J t) (u t) (Ωs t) S (4 * r) (hsupp t)
    have hB (t) (i j : Fin n) : HasAmplitudeDerivativeBound
        (fun ξ z ↦ b t ξ z i j) (2 * (n + 1)) (Cpdo t) :=
      fun ξ is his ↦ hA t i j ξ is (by omega)
    apply norm_restricted_carrierNormal_sub_le_full_amplitudes
      (by have := row.isLt; omega) (4 * r) b hb hs Cpdo hB Uop
      (fun t ↦ hUnormal t) χ hχ (2 * (n + 1)) le_rfl (4 * tol)
    intro i j
    simpa only [b, d, J, u, Ωs, S, e, cp, f, angular,
      Bool.false_eq_true, ↓reduceIte, positiveDensityAmplitude, Pi.sub_apply, Matrix.sub_apply]
      using (hfull i j).2

end JanetCartan.ContinuumNormal.ActualConstruction
