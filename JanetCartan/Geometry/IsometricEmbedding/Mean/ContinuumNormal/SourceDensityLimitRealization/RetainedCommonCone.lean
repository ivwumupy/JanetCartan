module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.RetainedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.CommonCone
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.SupportedInputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Frequency

/-!
# Apply the original frozen kernel to the genuine density limit

Apply the actual unit-kernel realization to the normalized inverse range,
radial law and full mask buffer returned by
`NormalizedSelection.exists_finite_incidence_comparison_inputs`. The original
frozen phase, seed, scalar buffers and both measurements are retained.
Consumer: the zero branch of
`exists_initialized_source_family_coercivity` (`bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel NullTransport
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2 NormalizedSelection

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)

set_option quotPrecheck false in
local notation "angular₀" => angularMask zRoot (NormedSpace.normalize ηb) ha'
  (angularWidth_spec hηb hr').1

include hr hrr haa har'

/-- Construct the genuine zero-limit carrier on the supplied common radial
cone from the SAME original frozen kernel and retained geometry. Its companion
origin branch is identified with every supplied initialized frozen carrier by
dense tests. The conclusion gives the consumer's normal identity for arbitrary
valid amplitude witnesses, and preserves it under common measurement. Constants
precede the original local density class (`app:ch_background:prop:bg-normalized`,
`bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`). -/
theorem exists_retained_source_zero_density_limit_on_common_cone
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {β cJ : ℝ} {Vphase Lphase : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q₀))
      (physicalParameterSet zRoot (6 * a) ×ˢ dataSet zRoot ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q₀) (physicalParameterSet zRoot (6 * a))
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r))
      Vphase Lphase β cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot (6 * a),
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q₀ p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hVphase : IsOpen Vphase) (hLphase : Lphase ⊆ Vphase) (hcJ : 0 < cJ)
    (hslice : ∀ p ∈ physicalParameterSet zRoot (6 * a), ∀ u ∈ dataBox zRoot ηb (2 * r),
      ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q₀ p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) Z
    let u := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    let Ω := frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    let e₀ := normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1)
      ha' hcell angular₀ FixedCutoffs.highFrequency 0
    let a₀ := coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1)
    ∀ (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      {ρ τ : ℝ} (_hρ : 0 < ρ) (_hτ : 0 < τ)
      {W K : Set (InputVariables n)} (_hW : IsOpen W)
      (_hball : closedBall p₀ ρ ⊆ W) (_hK : IsCompact K) (_hWK : W ⊆ K)
      (_hKInput : K ⊆ symbolInputDomain zRoot ηb r (6 * a))
      (_houtput : closedBall q₀ τ ⊆ Ω)
      {I : Set ℝ} (_hI : IsOpen I) (_hII : Icc (0 : ℝ) 1 ⊆ I)
      (_hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W D.field.region)
      (_hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
      {δ ε ℓ : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε)
      (_hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
      (_hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
      (_hℓ : 0 < ℓ) (_hlow : 2 * ℓ ≤ 1)
      (_hrange : MapsTo (inverseCoordinates u) (closedBall q₀ τ) (closedBall p₀ ρ))
      (_hgap : ∀ p ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient Z) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
      (_hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ J p)
      (_hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v ∈ S,
        (x, v) ∈ closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') →
          (x, v) ∈ closedBall q₀ τ)
      (_hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport zRoot (r := a') ⊆ D.field.carrier),
    ∀ {Ωcommon : Set (Variables n × Euclidean 2)}
      (u₀ : Variables n × Euclidean 2 → SliceVariable n)
      (_huFreq : ∀ p ∈ Ωcommon, p.1.2.2 ≠ 0)
      (_huNormalizedRange : MapsTo
        (fun p ↦ inverseCoordinates u₀ (normalizeOutputRadius ℓ p)) Ωcommon (closedBall p₀ ρ))
      (_huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ωcommon,
        u₀ (scaleFrequency t p.1, p.2) = ((u₀ p).1, t • (u₀ p).2))
      (_huRight : ∀ p ∈ Ωcommon, transportAveragedGradient Z (inverseCoordinates u₀ p) = p.1.2.2)
      (_hbuffer : closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ∩
        {p | p.1.2.2 ≠ 0} ⊆ Ωcommon),
    ∃ M ≥ (0 : ℝ), ∃ B > (0 : ℝ),
    ∃ Ccommon : (rCommon : ℝ) → 0 < rCommon → 4 * rCommon < 1 / 2 → ℝ,
      (∀ rCommon hrCommon hCommonCell, 0 ≤ Ccommon rCommon hrCommon hCommonCell) ∧
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
      let w := fun (t : Bool) (p : Euclidean n × CarrierParameter) ↦ Real.sqrt (1 + v
        (if t then sourceDensityFootpointExtension T Y (0, p) else (0, parameter p.2)))
      let e := fun t ↦ weightNormal e₀ (w t)
      let d := fun t ↦ {a₀ with normal := fun p ↦ w t p • a₀.normal p}
      let b := fun t ↦ fullReflectedMatrixAmplitude (d t) J u₀ Ωcommon S
      ∃ hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (b t)),
      ∃ hA : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b t ξ z i j)
        (2 * (n + 1) + 1) B,
      ∃ hs : ∀ t ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b t ξ z i j),
      ∃ Vzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖Vzero‖ ≤ M ∧ ‖Vzero.adjoint‖ ≤ M ∧
        (∀ f : carrierInitialTestSpace n,
          Vzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e true) f.val) ∧
        (∀ f : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (e true) f) 2 (carrierMeasure n) ∧
          Vzero.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (e true) f) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e true) f.val) → Wop = Vzero) ∧
        ∀ Vfrozen : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Vfrozen (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral
              (normalizedCarrierData T Q₀ F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
                ha' hcell angular₀ FixedCutoffs.highFrequency 0) f.val) →
        ∀ t : Bool,
        let Vop := if t then Vzero else Vfrozen
        let Aop := vectorTwoPositionL2Operator (by have := row.isLt; omega)
          (4 * a') (b t) (hb t) (hs t) B (fun i j ξ is his ↦ hA t i j ξ is (by omega))
        ‖Vop‖ ≤ M ∧ ‖Vop.adjoint‖ ≤ M ∧
        (∀ f : carrierInitialTestSpace n,
          Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e t) f.val) ∧
        (∀ f : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (e t) f) 2 (carrierMeasure n) ∧
          Vop.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (e t) f) ∧
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
          realOutputCompression (transferOperator Aop) ∧
        (∀ (Rbox Bconsumer : ℝ)
          (hbconsumer : ContDiff ℝ ∞ (Function.uncurry (b t)))
          (hsconsumer : ∀ ξ i j, SupportedInCenteredBox Rbox (fun z ↦ b t ξ z i j))
          (hBconsumer : ∀ i j, HasAmplitudeDerivativeBound
            (fun ξ z ↦ b t ξ z i j) (2 * (n + 1)) Bconsumer),
          carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
            realOutputCompression (transferOperator
              (vectorTwoPositionL2Operator (by have := row.isLt; omega)
                Rbox (b t) hbconsumer hsconsumer Bconsumer hBconsumer))) ∧
        ∀ {rCommon : ℝ} (hrCommon : 0 < rCommon) (hCommonCell : 4 * rCommon < 1 / 2),
          6 * rCommon < a' →
          let χ := FixedCutoffs.periodic (n := n) hrCommon hCommonCell 1
          let eCommon := CommonMeasurement.commonChartData (e t) (closedBall 0 (4 * rCommon)) χ
          let VCommon := CommonMeasurement.restrictCarrier χ Vop
          let dCommon := coefficientsOfCarrier eCommon (FixedCutoffs.physical hrCommon 1)
          let bCommon := fullReflectedMatrixAmplitude dCommon J u₀ Ωcommon S
          ‖VCommon‖ ≤ M ∧
          (∀ f : carrierInitialTestSpace n,
            VCommon (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral eCommon f.val) ∧
          (∀ f : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eCommon f) 2 (carrierMeasure n) ∧
            VCommon.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral eCommon f) ∧
          ∃ hbCommon : ContDiff ℝ ∞ (Function.uncurry bCommon),
          ∃ hBCommon : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bCommon ξ z i j)
            (2 * (n + 1)) (Ccommon rCommon hrCommon hCommonCell * B),
          ∃ hsCommon : ∀ ξ i j, SupportedInCenteredBox (4 * rCommon) (fun z ↦ bCommon ξ z i j),
            dCommon = CommonMeasurement.restrictCoefficients (d t) (FixedCutoffs.physical hrCommon 1) ∧
            bCommon = CommonMeasurement.restrictAmplitude (b t) (FixedCutoffs.physical hrCommon 1) ∧
            carrierChannel VCommon ∘L (carrierChannel VCommon).adjoint =
              realOutputCompression (transferOperator
                (vectorTwoPositionL2Operator (by have := row.isLt; omega)
                  (4 * rCommon) bCommon hbCommon hsCommon
                  (Ccommon rCommon hrCommon hCommonCell * B) hBCommon)) := by
  classical
  intro Z J u Ω S e₀ a₀ p₀ q₀ ρ τ hρ hτ W K hW hball hK hWK hKInput
    houtput I hI hII hsegI hseg A δ ε ℓ hδ hε hfreq hfoot hℓ hlow
    hrange hgap hJlow hshell hsupportD Ωcommon u₀ huFreq huNormalizedRange huScale huRight hbuffer
  have hOinput : closedBall p₀ ρ ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hm := hKInput (hWK (hball hp))
    have ha : 0 < a := ha'.trans_le haa
    exact ⟨⟨hm.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hm.2⟩
  have huRange := NormalizedNormalLimit.inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range
    hℓ huFreq huNormalizedRange huScale
  obtain ⟨M, hM, B, hB, Ccommon, hCcommon, hrealize⟩ :=
    exists_retained_source_zero_density_limit_realization T Q₀ F row col Φ Y
      hηb hr hr' ha' hrr haa har' hcell hP hseed hF hi hrank hR hRT hRU hV houter
      hVP hb hY hzero hparam hL hs₀ hsource D hD har hcarrier hf hInv htrans
      hVphase hLphase hcJ hslice p₀ q₀ hρ hτ hW hball hK hWK hKInput houtput
      hI hII hsegI hseg A hδ hε hfreq hfoot hℓ hlow hrange hgap hJlow hshell hsupportD
  refine ⟨M, hM, B, hB, Ccommon, hCcommon, ?_⟩
  intro v hv hpos hinterval hvnorm w e d b
  let bold := fun t ↦ fullReflectedMatrixAmplitude (d t) J u Ω S
  have heq (t : Bool) : bold t = b t :=
    (zero_weighted_fullAmplitudes_eq_common_cone T Q₀ hP hηb hr har hcarrier hInv htrans
      F row col Φ Y hr' ha' hcell hrr haa har' hOinput u₀ huRange huRight hbuffer (w t) S).2.2
  choose hbold hAold hsold Vops hprops using fun t ↦ hrealize v hv hpos hinterval hvnorm t
  have hbnew (t : Bool) : ContDiff ℝ ∞ (Function.uncurry (b t)) := heq t ▸ hbold t
  have hAnew (t : Bool) : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b t ξ z i j)
      (2 * (n + 1) + 1) B := heq t ▸ hAold t
  have hsnew (t : Bool) : ∀ ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b t ξ z i j) :=
    heq t ▸ hsold t
  obtain ⟨hV0, hAdj0, htest0, _, huniq0, hadjoint0, _⟩ := hprops true
  refine ⟨hbnew, hAnew, hsnew, Vops true, hV0, hAdj0, htest0, hadjoint0, huniq0, ?_⟩
  intro Vfrozen hfrozen t Vop Aop
  have hfrozenEq : Vfrozen = Vops false := (hprops false).2.2.2.2.2.2.1 rfl Vfrozen hfrozen
  have hpick : Vop = Vops t := by
    dsimp only [Vop]
    cases t
    · exact hfrozenEq
    · rfl
  rw [hpick]
  obtain ⟨hV, hAdj, htest, _, _, hadjoint, _, hnormal, hcommon⟩ := hprops t
  have hn : 0 < n := by have := row.isLt; omega
  have hnormalCommon : carrierChannel (Vops t) ∘L (carrierChannel (Vops t)).adjoint =
      realOutputCompression (transferOperator Aop) :=
    realized_normal_eq_of_amplitude_witnesses hn (4 * a') (4 * a')
      (bold t) (b t) (hbold t) (hbnew t) (hsold t) (hsnew t) B B
      (fun i j ξ is his ↦ hAold t i j ξ is (by omega))
      (fun i j ξ is his ↦ hAnew t i j ξ is (by omega)) (heq t) _ hnormal
  refine ⟨hV, hAdj, htest, hadjoint, hnormalCommon, ?_, ?_⟩
  · intro Rbox Bconsumer hbconsumer hsconsumer hBconsumer
    exact realized_normal_eq_of_amplitude_witnesses hn (4 * a') Rbox
      (b t) (b t) (hbnew t) hbconsumer (hsnew t) hsconsumer B Bconsumer
      (fun i j ξ is his ↦ hAnew t i j ξ is (by omega)) hBconsumer rfl _ hnormalCommon
  · intro rCommon hrCommon hCommonCell hsmall χ eCommon VCommon dCommon bCommon
    obtain ⟨hM', htest', hadjoint', _, hbOld, hBOld, hsOld, hdOld, hbEqOld, hnOld⟩ :=
      hcommon hrCommon hCommonCell hsmall
    have hd : dCommon = CommonMeasurement.restrictCoefficients (d t)
        (FixedCutoffs.physical hrCommon 1) := hdOld
    have hmeas : fullReflectedMatrixAmplitude dCommon J u Ω S = bCommon := by
      change fullReflectedMatrixAmplitude dCommon J u Ω S =
        fullReflectedMatrixAmplitude dCommon J u₀ Ωcommon S
      rw [hd]
      simp only [CommonMeasurement.fullReflectedMatrixAmplitude_restrictCoefficients]
      exact congrArg (fun bb ↦ CommonMeasurement.restrictAmplitude bb
        (FixedCutoffs.physical hrCommon 1)) (heq t)
    have hbCommon : ContDiff ℝ ∞ (Function.uncurry bCommon) := hmeas ▸ hbOld
    have hBCommon : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bCommon ξ z i j)
        (2 * (n + 1)) (Ccommon rCommon hrCommon hCommonCell * B) := hmeas ▸ hBOld
    have hsCommon : ∀ ξ i j, SupportedInCenteredBox (4 * rCommon) (fun z ↦ bCommon ξ z i j) :=
      hmeas ▸ hsOld
    refine ⟨hM', htest', hadjoint', hbCommon, hBCommon, hsCommon, hdOld, ?_, ?_⟩
    · exact hmeas.symm.trans (hbEqOld.trans (congrArg
        (fun bb ↦ CommonMeasurement.restrictAmplitude bb (FixedCutoffs.physical hrCommon 1)) (heq t)))
    · exact realized_normal_eq_of_amplitude_witnesses hn (4 * rCommon) (4 * rCommon)
        _ bCommon hbOld hbCommon hsOld hsCommon _ _ hBOld hBCommon hmeas _ hnOld

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
