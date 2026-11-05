module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.NormalWitnesses
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.FrozenMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Measurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.ZeroAmplitude

/-!
# Realize the genuine normalized source-density limit

Construct the weighted carrier, its literal Hilbert adjoint and its full
reflected normal on the supplied conic geometry. The divided-footpoint and
origin-frozen weights remain distinct. The constants precede the original
local density class. Physical localization is only a regularity argument:
the original full amplitude and both measurement factors are retained.

Consumers: `exists_initialized_density_limit_coercivity_of_retained_geometry`
and `NormalizedNormalLimit.exists_source_family_controlled_half_gap`.
Sources: `app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol` and `bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ContinuumNormalReduction TransportSymbol TransportKernel
open NormalizedBackground.SourceGeometry CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity Pseudodifferential AmplitudeBound PeriodicLocalL2
open ActualConstruction

/-- Construct both literal zero-source carriers on the SAME supplied conic
geometry. The `true` branch is the genuine divided-footpoint limit; the `false`
branch is the distinct origin weight. Only the original unit carrier's
substitution charts are supplied. All weighted regularity, finite-kernel
bounds, L² realization and normal identities are proved here. The normal
identity survives the common measurement restriction. The initialized frozen
operator is identified separately by uniqueness of its literal test action
(`bg-normalized`, `bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`,
`bg-frame`). -/
theorem exists_source_zero_density_limit_realization
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry angular))
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hMeasR : 3 * r ≤ R)
    {V : Set CarrierParameter} (hV : IsOpen V)
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
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
    let a := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular
        FixedCutoffs.highFrequency 0) (FixedCutoffs.physical hr 1)
    let physicalPositions := {p : Variables n × Euclidean 2 |
      p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
    ∀ (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      {ρ τ : ℝ} (_hρ : 0 < ρ) (_hτ : 0 < τ)
      {W K : Set (InputVariables n)} (_hW : IsOpen W)
      (_hball : closedBall p₀ ρ ⊆ W) (_hK : IsCompact K) (_hWK : W ⊆ K)
      {O : Set (Variables n × Euclidean 2)} (_hO : IsOpen O)
      (_houtput : closedBall q₀ τ ⊆ O)
      {I : Set ℝ} (_hI : IsOpen I) (_hII : Icc (0 : ℝ) 1 ⊆ I)
      (_hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W D.field.region)
      (_hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
      {δ ε Cupper ℓ : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε)
      (_hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
      (_hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
      (_hCupper : 0 ≤ Cupper) (_hℓ : 0 < ℓ) (_hℓone : ℓ ≤ 1) (_hlow : Cupper * ℓ ≤ 1)
      {S : Set (Euclidean 2)} (_hS : IsCompact S)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      {Ω : Set (Variables n × Euclidean 2)} (_hΩ : IsOpen (Ω ∩ physicalPositions)) (_hOΩ : O ⊆ (Ω ∩ physicalPositions))
      (_hu : ContDiffOn ℝ ∞ u (Ω ∩ physicalPositions))
      (_hrange : MapsTo (inverseCoordinates u) (closedBall q₀ τ) (closedBall p₀ ρ))
      (_hgap : ∀ p ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient Z) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
      (_heq : ∀ p ∈ (Ω ∩ physicalPositions), transportAveragedGradient Z (inverseCoordinates u p) = p.1.2.2)
      (_hJne : ∀ p ∈ W, J p ≠ 0)
      (_hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ J p)
      {Uinput Zmask : Set (InputVariables n)}
      (_hJ : ContDiffOn ℝ ∞ J Uinput)
      (_hInputJ : ∀ p ∈ Uinput, J p ≠ 0)
      (_hInputFreq : ∀ p ∈ Uinput, p.2.2 ≠ 0)
      (_hend : ∀ side, MapsTo (densityEndpoint side) Uinput D.field.region)
      (_hmap : MapsTo (inverseCoordinates u) (Ω ∩ physicalPositions) Uinput)
      (_hmask : ∀ p ∈ Uinput, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
        a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
      (_hpunctured : closure (augmentedTransportGradient Z '' Zmask) ∩
        {p | p.1.2.2 ≠ 0} ⊆ (Ω ∩ physicalPositions))
      (_hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v ∈ S,
        (x, v) ∈ closure (augmentedTransportGradient Z '' Zmask) →
          (x, v) ∈ closedBall q₀ τ)
      (_hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ (Ω ∩ physicalPositions) ↔ p ∈ (Ω ∩ physicalPositions))
      (_huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ (Ω ∩ physicalPositions),
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
      (_hJScale : ∀ t : ℝ, 0 < t → ∀ p ∈ (Ω ∩ physicalPositions),
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p))
      (_hupper : ∀ p ∈ (Ω ∩ physicalPositions), ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
      (Zp : Set CarrierParameter) (_hZp : IsCompact Zp)
      (_hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
      (_hsupportD : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ D.field.carrier)
      (_hchartR : 4 * r < R),
    let e₀ := normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1)
      hr hcell angular FixedCutoffs.highFrequency 0
    ∀ (charts : ∀ (Q : ℝ), 1 ≤ Q → ∀ x, x ∈ e₀.outputChart →
        ∀ y, y ∈ e₀.outputChart →
          ChartInputs e₀ (radialCarrierMask FixedCutoffs.radialRegularization Q) x y)
      (symbols : ∀ Q hQ x hx y hy, SymbolInputs (charts Q hQ x hx y hy))
      (_hSymCoeff : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).coefficients =
        regularizedCoefficients a FixedCutoffs.radialRegularization Q)
      (_hSymJac : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).jacobian = J)
      (_hSymInv : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).inverse = u)
      (_hSymDom : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).domain = Ω)
      (_hSymSpec : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).spectatorSupport = S)
      (_hSymInput : ∀ Q hQ x hx y hy, Uinput ⊆ (symbols Q hQ x hx y hy).inputDomain)
      (Cfreq : ℝ) (_hCfreq : 0 ≤ Cfreq)
      (_hcomparison : ∀ p ∈ Ω ∩ physicalPositions, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖),
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
      ∀ t : Bool,
      let w := fun p : Euclidean n × CarrierParameter ↦ Real.sqrt (1 + v
        (if t then sourceDensityFootpointExtension T Y (0, p) else (0, parameter p.2)))
      let e := weightNormal e₀ w
      let d := {a with normal := fun p ↦ w p • a.normal p}
      let b := fullReflectedMatrixAmplitude d J u Ω S
      ∃ hb : ContDiff ℝ ∞ (Function.uncurry b),
      ∃ hA : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        (2 * (n + 1) + 1) B,
      ∃ hs : ∀ ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ b ξ z i j),
      ∃ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖Vop‖ ≤ M ∧ ‖Vop.adjoint‖ ≤ M ∧
        (∀ f : carrierInitialTestSpace n,
          Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vop f x = 0) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → Wop = Vop) ∧
        (∀ f : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e f) 2 (carrierMeasure n) ∧
          Vop.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral e f) ∧
        (t = false → ∀ Vfrozen : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Vfrozen (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral
              (normalizedCarrierData T Q₀ F row col Φ Y (fun q ↦ Real.sqrt (1 + v q))
                hr hcell angular FixedCutoffs.highFrequency 0) f.val) → Vfrozen = Vop) ∧
        let Aop := vectorTwoPositionL2Operator (by have := row.isLt; omega)
          (4 * r) b hb hs B (fun i j ξ is his ↦ hA i j ξ is (by omega))
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
          realOutputCompression (transferOperator Aop) ∧
        ∀ {rCommon : ℝ} (hrCommon : 0 < rCommon) (hCommonCell : 4 * rCommon < 1 / 2),
          6 * rCommon < r →
          let χ := FixedCutoffs.periodic (n := n) hrCommon hCommonCell 1
          let eCommon := CommonMeasurement.commonChartData e (closedBall 0 (4 * rCommon)) χ
          let VCommon := CommonMeasurement.restrictCarrier χ Vop
          let multiplier := freezingVectorPhysicalMultiplier (FixedCutoffs.physical hrCommon 1)
            (FixedCutoffs.physical hrCommon 1).continuous (FixedCutoffs.physical hrCommon 1).hasCompactSupport
          ‖VCommon‖ ≤ M ∧
          (∀ f : carrierInitialTestSpace n,
            VCommon (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral eCommon f.val) ∧
          (∀ f : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eCommon f) 2 (carrierMeasure n) ∧
            VCommon.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral eCommon f) ∧
          carrierChannel VCommon ∘L (carrierChannel VCommon).adjoint =
            realOutputCompression (transferOperator (multiplier ∘L Aop ∘L multiplier)) ∧
          let dCommon := coefficientsOfCarrier eCommon (FixedCutoffs.physical hrCommon 1)
          let bCommon := fullReflectedMatrixAmplitude dCommon J u Ω S
          ∃ hbCommon : ContDiff ℝ ∞ (Function.uncurry bCommon),
          ∃ hBCommon : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ bCommon ξ z i j)
            (2 * (n + 1)) (Ccommon rCommon hrCommon hCommonCell * B),
          ∃ hsCommon : ∀ ξ i j, SupportedInCenteredBox (4 * rCommon) (fun z ↦ bCommon ξ z i j),
            dCommon = CommonMeasurement.restrictCoefficients d (FixedCutoffs.physical hrCommon 1) ∧
            bCommon = CommonMeasurement.restrictAmplitude b (FixedCutoffs.physical hrCommon 1) ∧
            carrierChannel VCommon ∘L (carrierChannel VCommon).adjoint =
              realOutputCompression (transferOperator
                (vectorTwoPositionL2Operator (by have := row.isLt; omega)
                  (4 * rCommon) bCommon hbCommon hsCommon
                  (Ccommon rCommon hrCommon hCommonCell * B) hBCommon)) := by
  classical
  let s := 2 * (n + 1) + 1
  obtain ⟨Mc, hMc, Bc, hBc, hcoeff⟩ :=
    exists_source_zero_density_coefficient_controls T Q₀ F row col Φ Y hr hcell
      angular FixedCutoffs.highFrequency (FixedCutoffs.physical hr 1)
      hP hseed hF hi hrank hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource
      D hD (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha.contDiffOn
      FixedCutoffs.highFrequency_smooth.contDiffOn
  intro Z J a physicalPositions p₀ q₀ ρ τ hρ hτ W K hW hball hK hWK O hO houtput I hI hII hsegI hseg
    A δ ε Cupper ℓ hδ hε hfreq hfoot hCupper hℓ hℓone hlow S hS
    u Ω hΩ hOΩ hu hrange hgap heq hJne hJlow Uinput Zmask hJ hInputJ hInputFreq
    hend hmap hmask hpunctured hshell hcone huScale hJScale hupper Zp hZp hangular
    hsupportD hchartR e₀ charts symbols hSymCoeff hSymJac hSymInv hSymDom hSymSpec
    hSymInput Cfreq hCfreq hcomparison
  let Ωlocal := Ω ∩ {p | p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
  have hZ : ContDiffOn ℝ ∞ Z D.field.region :=
    (normalizedTransportPosition_zero_smooth T Q₀ hP).mono
      (fun p hp ↦ ⟨mem_univ _, hVP (hD hp).2⟩)
  let Mp := cNorm D.field.carrier 3 Z
  let Bp := 1 + cNorm D.field.carrier (s + 2) Z
  have hMp : 0 ≤ Mp := cNorm_nonneg ..
  have hBp : 0 ≤ Bp := add_nonneg zero_le_one (cNorm_nonneg ..)
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, hconstruct⟩ :=
    exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms
      (N := N) (CanonicalConic.adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hball hK hWK
      hO houtput D.field.isOpen_region (isCompact_closedBall ..) D.field.ball_subset
      hI hII hsegI hseg A hMp hMc.le hBc hδ hε hBp hfreq D hfoot
      hCupper hℓ hℓone hlow hS s (by dsimp [s]; omega)
      FixedCutoffs.highFrequency_smooth (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
      FixedCutoffs.radialRegularization_smooth FixedCutoffs.radialRegularization_compact
      (fun _ ht ↦ FixedCutoffs.radialRegularization_one ht)
  have hn : 0 < n := by have := row.isLt; omega
  choose Ccommon hCcommon hcommonRealize using fun rCommon hrCommon hCommonCell ↦
    exists_commonMeasurement_literal_normal hn (r := rCommon) hrCommon hCommonCell
  refine ⟨Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * r) * Cnorm)),
    Real.sqrt_nonneg _, Cpdo, hCpdo, Ccommon, hCcommon, ?_⟩
  intro v hv hpos hinterval hvnorm t w e d b
  obtain ⟨hcActual, hcFrozen⟩ := hcoeff v hv hpos hinterval hvnorm
  have hc : D.Controls s Mc Bc 1 d := by
    cases t
    · exact hcFrozen
    · exact hcActual
  have hreg : PrimitiveRegularity d J Uinput := {
    leftMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.fst
    rightMeasurement := (FixedCutoffs.physical hr 1).contDiff.comp_contDiffOn contDiffOn_fst.snd
    angular := ha
    high := FixedCutoffs.highFrequency_smooth
    leftNormal := hc.normal.smooth.comp (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightNormal := hc.normal.smooth.comp (densityEndpoint_contDiff true).contDiffOn (hend true)
    leftReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff false).contDiffOn (hend false)
    rightReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
      (densityEndpoint_contDiff true).contDiffOn (hend true)
    jacobian := hJ
    jacobian_ne_zero := hInputJ
    covector_ne_zero := hInputFreq }
  let E := ball (0 : Euclidean n) R ×ˢ V
  obtain ⟨hActual, hActualRange, hFrozen, hFrozenRange⟩ :=
    source_zero_density_labels_regular T hR hV hY hzero hparam hs₀ hsource
  let g := fun p : Euclidean n × CarrierParameter ↦
    if t then sourceDensityFootpointExtension T Y (0, p) else (0, parameter p.2)
  have hg : ContinuousOn g E := by
    cases t
    · exact hFrozen.continuousOn
    · exact hActual.continuousOn
  have hgRange : MapsTo g E (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) := by
    have hs : closedBall ((0 : Euclidean (n - 1)), zCell) (L / 16) ⊆
        ball ((0 : Euclidean (n - 1)), zCell) (L / 4) := closedBall_subset_ball (by linarith)
    cases t
    · exact fun p hp ↦ hs (hFrozenRange hp)
    · exact fun p hp ↦ hs (hActualRange hp)
  have hw : ContinuousOn w E :=
    Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.add (hv.continuousOn.comp hg hgRange))
  let w' := E.indicator w
  have hw' : Measurable w' := by
    convert hw.measurable_piecewise (g := fun _ ↦ (0 : ℝ)) continuousOn_const
      (isOpen_ball.prod hV).measurableSet using 1
    funext p
    by_cases hp : p ∈ E <;> simp [w', hp]
  have hweight : ∀ x z η, e₀.measurementCutoff x ≠ 0 → e₀.angularCutoff z η ≠ 0 →
      w (e₀.chartPoint x, z) = w' (e₀.chartPoint x, z) := by
    intro x z η hx hz
    have hz' : z ∈ Zp := by
      by_contra hn
      exact hz (hangular z hn η)
    have hx' : FixedCutoffs.physical hr 1 (e₀.chartPoint x) ≠ 0 := hx
    have hp : (e₀.chartPoint x, z) ∈ E := hD (D.field.ball_subset
      (hsupportD (show (e₀.chartPoint x, z) ∈ tsupport (FixedCutoffs.physical hr 1) ×ˢ Zp from
        ⟨subset_tsupport _ hx', hz'⟩)))
    exact (indicator_of_mem hp w).symm
  have hq : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      reducedCovector e p.1 (e.covector p.1 p.2)) D.field.region := by
    exact (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp hc.reduced.smooth)
  have hkernel := supported_kernel_stronglyMeasurable e hr hcell angular
    rfl rfl rfl rfl rfl D.field.isOpen_region hZ.continuousOn
    hc.normal.smooth.continuousOn hq.continuousOn ha.continuous hangular
    (hsupportD.trans D.field.ball_subset)
  obtain ⟨Cmask, hCmask, hamp⟩ := exists_supported_carrierAmplitude_bound e hr hcell angular
    rfl rfl rfl rfl (isCompact_closedBall D.field.center D.field.radius)
    (hc.normal.smooth.continuousOn.mono D.field.ball_subset)
    (hq.continuousOn.mono D.field.ball_subset) ha.continuous hZp hangular hsupportD
  have hpointR : ∀ x ∈ e₀.outputChart, e₀.chartPoint x ∈ ball (0 : Euclidean n) R :=
    fun x hx ↦ (closedBall_subset_ball hchartR) hx
  let charts' := fun Q hQ x hx y hy ↦ weightedChartInputs (charts Q hQ x hx y hy) w w' hw' hweight
  let symbols' := fun Q hQ x hx y hy ↦ weightedLocalSymbolInputs (symbols Q hQ x hx y hy)
    w w' hw' hweight isOpen_ball (hpointR x hx) (hpointR y hy) (hSymInput Q hQ x hx y hy)
    (by simpa only [hSymInv Q hQ x hx y hy, hSymDom Q hQ x hx y hy] using hmap)
    hreg.leftNormal hreg.rightNormal
  have hcoeff' : ∀ Q hQ x hx y hy, (symbols' Q hQ x hx y hy).coefficients =
      regularizedCoefficients d FixedCutoffs.radialRegularization Q := by
    intro Q hQ x hx y hy
    have hh := hSymCoeff Q hQ x hx y hy
    have hupdate := congrArg (fun a : Coefficients n N ↦
      {a with normal := fun p ↦ w p • a.normal p}) hh
    exact hupdate
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * r := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)))
  have hRfreq : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_snd.snd
  have hX : {p : Variables n | ‖p.2.2‖ = ℓ} ⊆ {p | p.2.2 ≠ 0} := by
    intro p hp
    exact norm_ne_zero_iff.mp (hp.trans_ne hℓ.ne')
  obtain ⟨_, _, _, _, _, _, _, hb', hA, Vop, hVop, hVadj, htest, hsupp, huniq, hadj, _, hnormal⟩ :=
    hconstruct d Z u J Ωlocal Uinput Zmask {p | ‖p.2.2‖ = ℓ} {p | p.2.2 ≠ 0} 1
      hZ le_rfl hΩ hOΩ hu hrange hgap heq (fun _ _ ↦ rfl) hJne hJlow le_rfl
      (by simp only [Bp, mul_one]; exact le_rfl) hreg hmap hmask hRfreq hX
      (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
      (fun x hx z hz hxz ↦ hshell x hx z hz hxz) hc hcone huScale hJScale hupper
      hpunctured (CanonicalConic.scaleFrequency_mem_fixed_sphere hℓ)
      hn (4 * r) hsupport (by dsimp [s]; omega) e Zp hZp hangular Cmask hCmask hkernel hamp
      (closedBall 0 (4 * r)) (FixedCutoffs.closedBall_four_subset_cell hcell) rfl (fun _ _ ↦ rfl)
      (FixedCutoffs.physical hr 2) (fun _ hx ↦ FixedCutoffs.physical_eq_zero_outside_four hr 2 hx)
      (FixedCutoffs.physical hr 2).contDiff (FixedCutoffs.physical hr 2).hasCompactSupport
      (fun _ hx ↦ FixedCutoffs.source_one_on_measurement hr hx)
      charts' symbols' hcoeff' (fun Q hQ x hx y hy ↦ hSymJac Q hQ x hx y hy)
      (fun Q hQ x hx y hy ↦ hSymInv Q hQ x hx y hy)
      (fun Q hQ x hx y hy ↦ by
        change (symbols Q hQ x hx y hy).domain ∩ _ = Ωlocal
        rw [hSymDom Q hQ x hx y hy])
      (fun Q hQ x hx y hy ↦ hSymSpec Q hQ x hx y hy) Cfreq hCfreq hcomparison
  have hd : {d with high := FixedCutoffs.highFrequency} = d := rfl
  simp only [hd, mul_one] at hb' hA hVop hVadj hnormal
  have hlocal : fullReflectedMatrixAmplitude d J u Ωlocal S = b :=
    fullReflectedMatrixAmplitude_inter_fixed_measurement_ball hr hMeasR d rfl J u Ω S
  have hbFull : ContDiff ℝ ∞ (Function.uncurry b) := hlocal ▸ hb'
  have hAFull : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) s Cpdo := by
    rw [← hlocal]
    exact hA
  have hsFull := fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ω S (4 * r) hsupport
  have hnormalFull := realized_normal_eq_of_amplitude_witnesses hn (4 * r) (4 * r)
    _ b hb' hbFull (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ωlocal S (4 * r) hsupport)
    hsFull Cpdo Cpdo (fun i j ξ is his ↦ hA i j ξ is (by dsimp [s]; omega))
    (fun i j ξ is his ↦ hAFull i j ξ is (by dsimp [s]; omega)) hlocal Vop hnormal
  refine ⟨hbFull, hAFull, hsFull,
    Vop, hVop, hVadj, htest, hsupp, huniq, hadj, ?_, hnormalFull, ?_⟩
  · intro ht Vfrozen hfrozen
    subst t
    apply (originWeighted_realization_eq_initialized T Q₀ F row col Φ Y hr hcell
      angular FixedCutoffs.highFrequency hzero
      (fun z hz ↦ hparam (0, z) ⟨mem_ball_self hR, hz⟩) ?_ v Vop Vfrozen htest hfrozen).symm
    intro z η hz
    have hz' : z ∈ Zp := by
      by_contra hh
      exact hz (hangular z hh η)
    have hx : (0 : Euclidean n) ∈ tsupport (FixedCutoffs.physical hr 1) := by
      apply subset_tsupport
      have he : FixedCutoffs.physical hr (1 : Fin 3) (0 : Euclidean n) = 1 :=
        (interior_subset (s := {x : Euclidean n | FixedCutoffs.physical hr 1 x = 1}))
          (FixedCutoffs.physical_plateau hr 1
          (show (0 : Euclidean n) ∈ closedBall 0 (((1 : Fin 3) + 1 : ℝ) * r) from
            mem_closedBall_self (by positivity)))
      exact he.trans_ne one_ne_zero
    exact (hD (D.field.ball_subset (hsupportD
      (show ((0 : Euclidean n), z) ∈ tsupport (FixedCutoffs.physical hr 1) ×ˢ Zp from
        ⟨hx, hz'⟩)))).2
  intro rCommon hrCommon hCommonCell hcommon χ eCommon VCommon multiplier
  obtain ⟨hbound, htestC, hadjC, _, hnormalC⟩ :=
    CommonMeasurement.fixed_common_restriction e hrCommon hr hCommonCell hcell hcommon
      rfl (fun _ _ ↦ rfl) rfl Vop htest hadj _ hnormalFull
  refine ⟨hbound.trans hVop, htestC, hadjC, hnormalC, ?_⟩
  exact hcommonRealize rCommon hrCommon hCommonCell e hr (by linarith)
    J u Ω S (4 * r) hbFull hsFull Cpdo
    (fun i j ξ is his ↦ hAFull i j ξ is (by dsimp [s]; omega)) Vop hnormalFull

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
