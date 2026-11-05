module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedWeightedShell
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.ShellTransfer

/-!
# Full-amplitude variation with independently retained slice inverses

Use the existing retained spectral geometry at each frame separately. The
canonical inverse maps, outer symbol domains, common augmented input ball,
mask support and scalar class remain fixed as in the selected row. Auxiliary
slice inverse domains and constants are never identified across frames.
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

/-- Derive full complex and reflected amplitude differences from immersion
closeness on the actual retained masks, using the existing
`RetainedSpectralGeometry` independently at the reference and current frames.
The current slice inverse witnesses are chosen after the immersion threshold;
no common existential slice domain or slice Jacobian constant is required.
The common augmented comparison ball, outer domains, original density class,
Lebesgue spectator measure and reflected factor four are unchanged.

Producer: `NormalizedSelection.exists_finite_incidence_comparison_inputs`.
Consumer: variation of the same selected row in
`ActualConstruction.norm_physicalNormal_sub_le_image_and_full_amplitudes`.
Sources: `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_retained_conic_fullAmplitude_comparison_of_spectral_geometry
    {c₁ C : ℝ} (hP : P.IsValid c₁ C)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hRc : 0 < Rc) (hB : 0 ≤ B) (hτ : 0 < τ)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hKFU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hKU : K ⊆ CoefficientBounds.inputDomain T)
    (hx : MapsTo Prod.fst K (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {rOuter aOuter : ℝ}
    (hηb : ηb ≠ 0) (hrOuter : 0 < rOuter)
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
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {gap : ℝ} (hgap : 0 < gap)
    (hgap₀ : ∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (transportPosition T c₀.Q) p)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ Ki, η ≤ ‖p.2.2‖)
    (hcontains : ∀ p ∈ Ki, D.Contains p)
    (hWDom : W ⊆ symbolInputDomain zRoot ηb rOuter (6 * aOuter))
    {r rAngular : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hrAngular : 0 < rAngular) (hrr : rAngular ≤ rOuter)
    (haa : r ≤ aOuter) (har : r ≤ rAngular)
    (hQradius : ∀ p ∈ Q, ‖p.1.2.2‖ = 1 / 4)
    (hne : ∀ p ∈ Ωi, p.1.2.2 ≠ 0)
    (hscale : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ωi ↔ p ∈ Ωi)
    (hspectral₀ : RetainedFrozen.RetainedSpectralGeometry T c₀.Q zRoot ηb rOuter aOuter)
    (hdom₀ : Ωi ⊆ symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter))
    (hnorm₀ : MapsTo (fun q ↦ inverseCoordinates (symbolInverse T c₀.Q zRoot ηb rOuter (6 * aOuter))
      (normalizeOutputRadius (1 / 4) q)) Ωi Ki)
    (hbuffer₀ : closure (augmentedTransportGradient (transportPosition T c₀.Q) ''
      conicMaskSupport zRoot ηb rAngular r) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)
    (hshell₀ : ∀ p : Variables n, ‖p.2.2‖ = 1 / 4 → ∀ v ∈ closedBall (spectatorCenter zRoot) (r / 2),
      (p, v) ∈ closure (augmentedTransportGradient (transportPosition T c₀.Q) ''
        conicMaskSupport zRoot ηb rAngular r) → (p, v) ∈ Q)
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
      MapsTo (densityFootpoint T c.inverse) D.field.region
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) →
      RetainedFrozen.RetainedSpectralGeometry T c.Q zRoot ηb rOuter aOuter →
      Ωi ⊆ symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter) →
      MapsTo (fun q ↦ inverseCoordinates (symbolInverse T c.Q zRoot ηb rOuter (6 * aOuter))
        (normalizeOutputRadius (1 / 4) q)) Ωi Ki →
      (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T c.Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ki, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T c.Q) p) →
      (closure (augmentedTransportGradient (transportPosition T c.Q) ''
        conicMaskSupport zRoot ηb rAngular r) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi) →
      (∀ p : Variables n, ‖p.2.2‖ = 1 / 4 → ∀ v ∈ closedBall (spectatorCenter zRoot) (r / 2),
        (p, v) ∈ closure (augmentedTransportGradient (transportPosition T c.Q) ''
          conicMaskSupport zRoot ηb rAngular r) → (p, v) ∈ Q) →
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
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude d (symbolJacobian T c.Q) u
          (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j -
          fullComplexMatrixAmplitude dref (symbolJacobian T c₀.Q) uref
          (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j) m tol ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude d (symbolJacobian T c.Q) u
          (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j -
          fullReflectedMatrixAmplitude dref (symbolJacobian T c₀.Q) uref
          (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S ξ z i j) m (4 * tol) := by
  obtain ⟨_har₀, _hcarrier₀, G₀, b₀, cJ₀, V₀, L₀, hcJ₀, _hV₀, hLV₀,
    hf₀, hInv₀, htrans₀, _hslice₀⟩ := hspectral₀
  let angular := angularMask zRoot (NormedSpace.normalize ηb) hr (angularWidth_spec hηb hrAngular).1
  let u₀ := symbolInverse T c₀.Q zRoot ηb rOuter (6 * aOuter)
  let J₀ := transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T c₀.Q)
  let S := closedBall (spectatorCenter zRoot) (r / 2)
  have hu₀ : ContDiffOn ℝ ∞ u₀ Ωi :=
    (symbolInverse_smooth T c₀.Q hηb hrOuter hInv₀ htrans₀ hLV₀).mono hdom₀
  have hrange₀ : MapsTo (inverseCoordinates u₀) Q Ki := by
    intro p hp
    have hn := hnorm₀ (hQΩi hp)
    change inverseCoordinates u₀ (normalizeOutputRadius (1 / 4) p) ∈ Ki at hn
    rwa [normalizeOutputRadius_eq_self (by norm_num) (hQradius p hp)] at hn
  have hJ₀ : ContDiffOn ℝ ∞ J₀ W :=
    (transportAbsoluteJacobian_smooth T c₀.Q hηb hrOuter hf₀ hInv₀ htrans₀ hcJ₀).mono hWDom
  have hangular : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2) :=
    angularMask_smooth ..
  have hshellComparison := exists_retained_conic_weighted_shell_comparison T hdomain hgeometry hP
    hΩ hK hKΩ hRc hB hτ hbuffer hτeq hKFU hKU hx D hSK hSflow c₀ hF₀ hi₀ hrank₀
    hκmet hκnormal hlow₀ hmet₀ hnormal₀ hR initial hi hipos hfoot₀ hDV
    hKi hconv hW hKiW hBi hWBi hQ hΩi hQΩi hIt hIIt hsegT hseg u₀ hu₀ A
    (adaptedSliceCoordinates T) hrange₀
    (fun p hp ↦ transportAveragedGradient_symbolInverse T c₀.Q hηb hrOuter hInv₀ htrans₀ (hdom₀ hp))
    hgap hgap₀ hJ₀ hη hfreq hcontains hr hcell angular FixedCutoffs.highFrequency
    (FixedCutoffs.physical hr 1).contDiff.contDiffOn hangular.contDiffOn FixedCutoffs.highFrequency_smooth
    (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
    (fun _ ht ↦ FixedCutoffs.highFrequency_one ht) m (by omega)
  obtain ⟨Cfull, hCfull, hfull⟩ := AmplitudeDifference.exists_fullAmplitude_sub_bounds_of_supported_shell
    (N := N) m hreserve (isCompact_closedBall (spectatorCenter zRoot) (r / 2)) hQ
    (Cupper := 2) (ℓ := 1 / 4) (B := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro tol htol
  obtain ⟨δ, hδ, hmatrix⟩ := hshellComparison (tol / Cfull) (div_pos htol hCfull)
  refine ⟨δ, hδ, ?_⟩
  intro F c hF him hrank hlow hmet hnormal hfoot hspectral hdom hnorm hdiffGap hJgap
    hbufferCurrent hshellCurrent hsmall d₀ horder v hv hvm hpos
  obtain ⟨_har, _hcarrier, G, b, cJ, V, Louter, hcJ, _hV, hLV,
    hf, hInv, htrans, _hslice⟩ := hspectral
  dsimp only
  let u := symbolInverse T c.Q zRoot ηb rOuter (6 * aOuter)
  let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T c.Q)
  let d := TransportKernel.coefficientsOfCarrier
    (data T c.Q F row col c.forward c.inverse (fun y ↦ initial y * Real.sqrt (1 + v y))
      hr hcell angular FixedCutoffs.highFrequency) (FixedCutoffs.physical hr 1)
  let dref := TransportKernel.coefficientsOfCarrier
    (data T c₀.Q F₀ row col c₀.forward c₀.inverse (fun y ↦ initial y * Real.sqrt (1 + v y))
      hr hcell angular FixedCutoffs.highFrequency) (FixedCutoffs.physical hr 1)
  have hu : ContDiffOn ℝ ∞ u Ωi :=
    (symbolInverse_smooth T c.Q hηb hrOuter hInv htrans hLV).mono hdom
  have hrange : MapsTo (inverseCoordinates u) Q Ki := by
    intro p hp
    have hn := hnorm (hQΩi hp)
    change inverseCoordinates u (normalizeOutputRadius (1 / 4) p) ∈ Ki at hn
    rwa [normalizeOutputRadius_eq_self (by norm_num) (hQradius p hp)] at hn
  have hJ : ContDiffOn ℝ ∞ J W :=
    (transportAbsoluteJacobian_smooth T c.Q hηb hrOuter hf hInv htrans hcJ).mono hWDom
  have hmatrix' := hmatrix F c u hF him hrank hlow hmet hnormal hfoot hu hrange
    (fun p hp ↦ transportAveragedGradient_symbolInverse T c.Q hηb hrOuter hInv htrans (hdom hp))
    hdiffGap hJgap hJ hsmall d₀ horder v hv hvm hpos
  have hreg := retained_originalDensity_primitiveRegularity_on_full_inverse_image c hP hRc hτ hKΩ hKU
    hF him hrank D hSK hSflow hR initial hi hipos hfoot hηb hrOuter hf hInv htrans hcJ
    hdom hne (by norm_num : (0 : ℝ) < 1 / 4) hnorm hcontains hr hcell angular
    FixedCutoffs.highFrequency hangular FixedCutoffs.highFrequency_smooth v hv hpos
  have hreg₀ := retained_originalDensity_primitiveRegularity_on_full_inverse_image c₀ hP hRc hτ hKΩ hKU
    hF₀ hi₀ hrank₀ D hSK hSflow hR initial hi hipos hfoot₀ hηb hrOuter hf₀ hInv₀ htrans₀ hcJ₀
    hdom₀ hne (by norm_num : (0 : ℝ) < 1 / 4) hnorm₀ hcontains hr hcell angular
    FixedCutoffs.highFrequency hangular FixedCutoffs.highFrequency_smooth v hv hpos
  let ap : Fin 2 → Coefficients n N := ![d, dref]
  let jp : Fin 2 → InputVariables n → ℝ := ![J, J₀]
  let up : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1) := ![u, u₀]
  let fp : Fin 2 → InputVariables n → Variables n × Euclidean 2 :=
    ![augmentedTransportGradient (transportPosition T c.Q),
      augmentedTransportGradient (transportPosition T c₀.Q)]
  let wp := fun i ↦ inverseCoordinates (up i) '' Ωi
  let zp : Fin 2 → Set (InputVariables n) := fun _ ↦ conicMaskSupport zRoot ηb rAngular r
  have hinput (i : Fin 2) : wp i ⊆ symbolInputDomain zRoot ηb rOuter (6 * aOuter) := by
    rintro _ ⟨p, hp, rfl⟩
    fin_cases i
    · exact symbolInverse_maps T c.Q hηb hrOuter hInv htrans (hdom hp)
    · exact symbolInverse_maps T c₀.Q hηb hrOuter hInv₀ htrans₀ (hdom₀ hp)
  have hresult := hfull ap jp up fp Ωi wp zp (tol / Cfull) (div_pos htol hCfull).le hΩi hQΩi
    (by intro i; fin_cases i; exact hreg; exact hreg₀)
    (by intro i; fin_cases i; exact hu; exact hu₀)
    (fun _ p hp ↦ ⟨p, hp, rfl⟩)
    (by
      intro i p hp
      fin_cases i
      · exact augmentedTransportGradient_symbolInverse T c.Q hηb hrOuter hInv htrans (hdom hp)
      · exact augmentedTransportGradient_symbolInverse T c₀.Q hηb hrOuter hInv₀ htrans₀ (hdom₀ hp))
    (by
      intro i p hp hl hr' hang
      have hηp := (hinput i hp).2.2.1
      fin_cases i <;> exact primitive_masks_mem_conicMaskSupport hηb hrAngular hr hηp hl hr' hang)
    (by intro i; fin_cases i; exact hbufferCurrent; exact hbuffer₀)
    (by intro i t ht; fin_cases i <;> exact FixedCutoffs.highFrequency_zero ht)
    (by
      intro i p hp
      fin_cases i
      · exact symbolInverse_norm_le_two T c.Q hηb hrOuter hInv htrans (hdom hp)
      · exact symbolInverse_norm_le_two T c₀.Q hηb hrOuter hInv₀ htrans₀ (hdom₀ hp))
    hscale
    (by
      intro i t ht p _
      fin_cases i
      · exact symbolInverse_scale_all T c.Q hηb hrOuter hInv htrans t ht p
      · exact symbolInverse_scale_all T c₀.Q hηb hrOuter hInv₀ htrans₀ t ht p)
    (by
      intro i t ht p hp
      fin_cases i
      · exact transportAbsoluteJacobian_scaling T c.Q hηb hrOuter hf hInv htrans
          (symbolInverse_maps T c.Q hηb hrOuter hInv htrans (hdom hp)) ht
      · exact transportAbsoluteJacobian_scaling T c₀.Q hηb hrOuter hf₀ hInv₀ htrans₀
          (symbolInverse_maps T c₀.Q hηb hrOuter hInv₀ htrans₀ (hdom₀ hp)) ht)
    (by
      intro p hp w hw hmem
      rcases hmem with hmem | hmem
      · exact hshellCurrent p hp w hw hmem
      · exact hshell₀ p hp w hw hmem)
    (fun t ht ↦ by
      simpa only [one_mul, ap, jp, up, d, dref, J, J₀, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Pi.sub_def] using (hmatrix' t ht).le)
  have hcancel : Cfull * (tol / Cfull) = tol := by field_simp
  have hcancel4 : (4 * Cfull) * (tol / Cfull) = 4 * tol := by rw [mul_assoc, hcancel]
  have he := retained_amplitudes_eq_on_common_conic_target T c.Q F row col c.forward c.inverse
    (fun y ↦ initial y * Real.sqrt (1 + v y)) hηb hrOuter hrAngular hr hrr haa har hcell
    hf hInv htrans hdom hbufferCurrent S
  have he₀ := retained_amplitudes_eq_on_common_conic_target T c₀.Q F₀ row col c₀.forward c₀.inverse
    (fun y ↦ initial y * Real.sqrt (1 + v y)) hηb hrOuter hrAngular hr hrr haa har hcell
    hf₀ hInv₀ htrans₀ hdom₀ hbuffer₀ S
  have hce : fullComplexMatrixAmplitude d J u Ωi S =
      fullComplexMatrixAmplitude d (symbolJacobian T c.Q) u
        (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S := he.2.1
  have hce₀ : fullComplexMatrixAmplitude dref J₀ u₀ Ωi S =
      fullComplexMatrixAmplitude dref (symbolJacobian T c₀.Q) u₀
        (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S := he₀.2.1
  have hre : fullReflectedMatrixAmplitude d J u Ωi S =
      fullReflectedMatrixAmplitude d (symbolJacobian T c.Q) u
        (symbolDomain T c.Q zRoot ηb rOuter (6 * aOuter)) S := he.2.2
  have hre₀ : fullReflectedMatrixAmplitude dref J₀ u₀ Ωi S =
      fullReflectedMatrixAmplitude dref (symbolJacobian T c₀.Q) u₀
        (symbolDomain T c₀.Q zRoot ηb rOuter (6 * aOuter)) S := he₀.2.2
  intro i j
  have hb := hresult i j
  dsimp only [ap, jp, up, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hb
  rw [hcancel, hcancel4] at hb
  rw [hce, hce₀, hre, hre₀] at hb
  exact hb

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
