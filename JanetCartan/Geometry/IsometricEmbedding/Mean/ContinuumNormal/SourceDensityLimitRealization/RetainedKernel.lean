module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.SupportedInputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Frequency

/-!
# Apply the original frozen kernel to the genuine density limit

Construct the unit substitution records and frequency comparison from the
retained buffered inverse, then apply the checked weighted realization.
The primitive ball, segment, shell and support inputs are those of
`exists_retained_joint_supported_geometry` and
`exists_finite_incidence_comparison_inputs`; the original seed and scalar
buffers are retained. Consumer: the zero branch of
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
open Pseudodifferential AmplitudeBound PeriodicLocalL2

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

/-- Realize both original zero-density weights with the actual retained
frozen kernel. Unit chart/symbol records and frequency comparison are
constructed, not supplied as additional interfaces. All density bounds and
literal normals follow from the existing producer. The endpoint retains the
same frozen carrier by dense-test uniqueness (`bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`). -/
theorem exists_retained_source_zero_density_limit_realization
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
      let d := {a₀ with normal := fun p ↦ w p • a₀.normal p}
      let b := fullReflectedMatrixAmplitude d J u Ω S
      ∃ hb : ContDiff ℝ ∞ (Function.uncurry b),
      ∃ hA : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        (2 * (n + 1) + 1) B,
      ∃ hs : ∀ ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b ξ z i j),
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
                ha' hcell angular₀ FixedCutoffs.highFrequency 0) f.val) → Vfrozen = Vop) ∧
        let Aop := vectorTwoPositionL2Operator (by have := row.isLt; omega)
          (4 * a') b hb hs B (fun i j ξ is his ↦ hA i j ξ is (by omega))
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
          realOutputCompression (transferOperator Aop) ∧
        ∀ {rCommon : ℝ} (hrCommon : 0 < rCommon) (hCommonCell : 4 * rCommon < 1 / 2),
          6 * rCommon < a' →
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
  intro Z J u Ω S e₀ a₀ p₀ q₀ ρ τ hρ hτ W K hW hball hK hWK hKInput
    houtput I hI hII hsegI hseg A δ ε ℓ hδ hε hfreq hfoot hℓ hlow
    hrange hgap hJlow hshell hsupportD
  have ha : 0 < a := ha'.trans_le haa
  have hchartR : 4 * a' < R := by
    have hx : (EuclideanSpace.single row (5 * a) : Euclidean n) ∈ ball 0 (6 * a) := by
      rw [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hm := (houter (show (EuclideanSpace.single row (5 * a), (zRoot 0, spectatorCenter zRoot)) ∈
      coefficientDomain zRoot r (6 * a) from ⟨hx, mem_ball_self hr, mem_ball_self (by positivity)⟩)).1
    rw [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)] at hm
    linarith
  let physicalPositions := {p : Variables n × Euclidean 2 |
    p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
  have hWInput : W ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hm := hKInput (hWK hp)
    exact ⟨⟨hm.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hm.2⟩
  have houtputLocal : closedBall q₀ τ ⊆ Ω ∩ physicalPositions := by
    intro p hp
    have hf := hfoot _ (hrange hp)
    exact ⟨houtput hp, (hD (D.field.ball_subset hf.2.2.2.2.1)).1,
      (hD (D.field.ball_subset hf.2.2.2.2.2)).1⟩
  have hopenLocal : IsOpen (Ω ∩ physicalPositions) :=
    (frozenSymbolDomain_open T Q₀ hηb hr hInv htrans hVphase hLphase).inter
      ((isOpen_ball.preimage continuous_fst.fst).inter (isOpen_ball.preimage continuous_fst.snd.fst))
  let E := ball (0 : Euclidean n) R ×ˢ V
  let D' : CoefficientNormCharts n := {D with field := {
    D.field with region := E
                 isOpen_region := isOpen_ball.prod hV
                 ball_subset := D.field.ball_subset.trans hD }}
  let Ui := frozenInputDomain zRoot ηb r (6 * a) ∩
    {p : InputVariables n | p.1.1 ∈ ball 0 R ∧ p.1.2 ∈ ball 0 R}
  have hlabel (p : InputVariables n) (hp : p ∈ frozenInputDomain zRoot ηb r (6 * a)) :
      p.2.1 ∈ V := by
    exact (houter (show ((0 : Euclidean n), p.2.1) ∈ coefficientDomain zRoot r (6 * a) from
      ⟨mem_ball_self (by positivity), hp.2.1, hp.1.1⟩)).2
  have hend : ∀ side, MapsTo (densityEndpoint side) Ui E := by
    intro side p hp
    cases side
    · exact ⟨hp.2.1, hlabel p hp.1⟩
    · exact ⟨hp.2.2, hlabel p hp.1⟩
  have hmap : MapsTo (inverseCoordinates u) (Ω ∩ physicalPositions) Ui :=
    fun p hp ↦ ⟨frozenSymbolInverse_maps T Q₀ hηb hr hInv htrans hp.1, hp.2⟩
  have hclosed : IsClosed {p : Variables n × Euclidean 2 |
      p.1.1 ∈ closedBall (0 : Euclidean n) (4 * a') ∧
      p.1.2.1 ∈ closedBall (0 : Euclidean n) (4 * a')} :=
    (isClosed_closedBall.preimage continuous_fst.fst).inter
      (isClosed_closedBall.preimage continuous_fst.snd.fst)
  have hpositions : closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ⊆
      {p : Variables n × Euclidean 2 | p.1.1 ∈ closedBall (0 : Euclidean n) (4 * a') ∧
        p.1.2.1 ∈ closedBall (0 : Euclidean n) (4 * a')} := by
    apply closure_minimal _ hclosed
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hpunctured : closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ∩
      {p | p.1.2.2 ≠ 0} ⊆ Ω ∩ physicalPositions := by
    intro p hp
    have hxy := hpositions hp.1
    exact ⟨frozenRefinedMaskImage_punctured_buffer T Q₀ hP hηb hr ha har hcarrier hf htrans
      hrr haa hp, closedBall_subset_ball hchartR hxy.1, closedBall_subset_ball hchartR hxy.2⟩
  obtain ⟨charts, symbols, hsymbols⟩ := exists_frozen_refined_kernel_inputs
    T Q₀ F row col Φ Y hηb hr hr' ha' hrr haa har' hcell
      hP har hcarrier hf hInv htrans hVphase hLphase hcJ
  exact exists_source_zero_density_limit_realization T Q₀ F row col Φ Y ha' hcell
    angular₀ (angularMask_smooth ..) hP hseed hF hi hrank hR hRT hRU
    (by linarith) hV hVP hb hY hzero hparam hL hs₀ hsource D' Subset.rfl
    p₀ q₀ hρ hτ hW hball hK hWK hopenLocal houtputLocal hI hII
    (fun t ht p hp ↦ hD (hsegI t ht hp)) hseg A hδ hε hfreq hfoot
    (Cupper := 2) (by norm_num) hℓ (by linarith) hlow (isCompact_closedBall ..) u
    hopenLocal Subset.rfl ((frozenSymbolInverse_smooth T Q₀ hηb hr hInv htrans hLphase).mono inter_subset_left)
    hrange hgap (fun _ hp ↦ frozenTransportGradient_inverse T Q₀ hP hηb hr har hcarrier hInv htrans hp.1)
    (fun p hp ↦ (frozenJacobian_pos T Q₀ hP hηb hr har hcarrier hInv htrans hf hcJ (hWInput hp)).ne')
    hJlow
    ((frozenJacobian_smooth T Q₀ hP hηb hr har hcarrier hInv htrans hf hcJ).mono inter_subset_left)
    (fun p hp ↦ (frozenJacobian_pos T Q₀ hP hηb hr har hcarrier hInv htrans hf hcJ hp.1).ne')
    (fun _ hp ↦ hp.1.2.2.1) hend hmap
    (fun p hp hx hy hang ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.1.2.2.1 hx hy hang)
    hpunctured hshell
    (fun t ht p ↦ by
      change ((scaleFrequency t p.1, p.2) ∈ Ω ∧ _) ↔ (p ∈ Ω ∧ _)
      rw [frozenSymbolDomain_smul_iff T Q₀ zRoot ηb r (6 * a) ht p]
      rfl)
    (fun _ ht _ hp ↦ frozenSymbolInverse_smul T Q₀ hηb hr hInv htrans hp.1 ht)
    (fun _ ht _ hp ↦ frozenJacobian_scaling T Q₀ hP hηb hr har hcarrier hf hInv htrans
      (frozenSymbolInverse_maps T Q₀ hηb hr hInv htrans hp.1) ht)
    (fun _ hp ↦ frozenSymbolInverse_norm_le_two T Q₀ hηb hr hInv htrans hp.1)
    (carrierSupport zRoot (r := a')) (carrierSupport_compact zRoot)
    (fun z hz η ↦ angularMask_zero_outside zRoot (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η) hsupportD hchartR
    charts symbols
    (fun Q hQ x hx y hy ↦ (hsymbols Q hQ x hx y hy).1)
    (fun Q hQ x hx y hy ↦ (hsymbols Q hQ x hx y hy).2.1)
    (fun Q hQ x hx y hy ↦ (hsymbols Q hQ x hx y hy).2.2.1)
    (fun Q hQ x hx y hy ↦ (hsymbols Q hQ x hx y hy).2.2.2.1)
    (fun Q hQ x hx y hy ↦ (hsymbols Q hQ x hx y hy).2.2.2.2.1)
    (fun Q hQ x hx y hy ↦ by
      rw [(hsymbols Q hQ x hx y hy).2.2.2.2.2.1]
      exact inter_subset_left)
    (frozenFrequencyBound T G) (frozenFrequencyBound_pos T G).le
    (fun _ hp ↦ frozenInverse_frequency_comparison T G Q₀ hηb hr hf hInv htrans hslice hp.1)

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
