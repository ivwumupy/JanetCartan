module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.CappedIncidenceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.DetectorMaskBuffers
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceRawAdjoint

/-!
# The same local conic geometry and normalized raw adjoint

Apply the raw-adjoint producer first, impose its prescribed spatial and angular
caps in the comparison geometry, and then realize those exact masks. No
analytic bound is an input and no independently selected mask is identified.
The finite selector can retain this simultaneous local conclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol FullPhaseCharts ActualPhase ActualComparison
open CarrierVariation.FamilyInputs PositiveReference
open NullTransport ActualFlow FlowAmplitude CarrierSobolev
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.NormalInputs ProjectedStressFrame
open ContinuumAdjoint.Canonical.PhaseExtension

/-- Construct the local comparison geometry and raw adjoint while retaining
full sampling support inside the original incidence domain. Both sampling
and adjoint caps are imposed BEFORE the masks are chosen. Current/frozen
conic domains, literal adjoints and all raw/density bounds use these same
masks. The original closed carrier set and complete detector direction set,
including their boundaries, lie in the supplied original chart. Consumers:
finite normalized selection and `Sampling.transverseDetectorIncidenceSupport_spec`
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-adjoint`,
`app:ch_background:prop:bg-normalized`, `app:ch_waves:thm:sampling`). -/
theorem exists_retained_normalized_cell_geometry_and_rawAdjoint_with_origin_targets {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρc Rc M τlead : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τlead) (hτR : τlead ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τlead))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {O : Set (Euclidean n)} (hO : IsOpen O) (hkO : NormedSpace.normalize k ∈ O)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    ∃ r a r' a' : ℝ, ∃ (_hr : 0 < r) (_ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a'),
      4 * a' < 1 / 2 ∧ 6 * a < cap ∧
      coefficientDomain z₀ r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
      6 * a < T.family.radius ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ hηb : ηb ≠ 0,
      MapsTo parameter (carrierSupport z₀ (r := a')) (parameterInterior P.radius) ∧
      (∀ z ∈ parameter '' carrierSupport z₀ (r := a'), ∀ θ ∈ closedDirections ηb r',
        NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      (∀ detector : Euclidean (n - 1) → ℂ,
        (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections ηb r') →
        ∀ z ∈ parameter '' carrierSupport z₀ (r := a'),
          ∀ θ ∈ Sampling.detectorDirectionSupport detector,
            NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      ∃ δ > (0 : ℝ),
    (∃ (D : CoefficientNormCharts n) (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      (ρ τ : ℝ) (W Bi : Set (InputVariables n)) (It : Set ℝ)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (ε gap : ℝ)
      (Qc Ωi : Set (Variables n × Euclidean 2)),
      originOutput q₀ = q₀ ∧
      Qc = compactTarget (1 / 4) q₀ τ ∧ Ωi = conicTarget (1 / 4) q₀ τ ∧
      0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ (ball (0 : Euclidean n) R ×ˢ V) ∩ coefficientDomain z₀ r (6 * a) ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (CarrierVariation.FamilyInputs.WideDensity.densityEndpoint side)
        W D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) ∧ 0 < gap ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = 1 / 4) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry T Q z₀ ηb r a ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi))) ∧
    ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ hcell : 4 * a' < 1 / 2,
      supportedChart (n := n) z₀ a' ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a') (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
        ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  obtain ⟨aMax, bMax, haMax, hbMax, _, χinitial, σ₀, hσ₀, hσ₁, hraw⟩ :=
    NormalizedFamily.exists_normalized_seed_rawAdjoint_for_submasks H hP T hUH hbounded
      hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans
      hR hRphysical hRU hV hVP hflow hz₀ hzV hk hinc hd hcap
  obtain ⟨aSampling, bSampling, haSampling, hbSampling, hsampling⟩ :=
    exists_incidence_detector_submask_caps T hP hz₀ hk hinc hO hkO
  obtain ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hasub, hbsub, δ, hδ, hgeometry⟩ :=
    exists_retained_incidence_comparison_inputs_with_mask_caps_and_origin_targets (N := embeddingDimension n)
      T hP hz₀ hk hinc hd hcap (lt_min haMax haSampling) (lt_min hbMax hbSampling) (ball (0 : Euclidean n) R ×ˢ V)
      (isOpen_ball.prod hV) ⟨mem_ball_self hR, hzV⟩
  obtain ⟨hparameter, hdirections, hdetector⟩ := hsampling a' r' _
    (hasub.trans (min_le_right _ _)) hηdir (hbsub.trans (min_le_right _ _))
  refine ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hparameter, hdirections, hdetector, δ, hδ,
    hgeometry, χinitial, σ₀, hσ₀, hσ₁, ?_⟩
  have hh := hraw a' _ ha' (angularWidth_spec hηb hr').1
    (hasub.trans (min_le_left _ _)) (hbsub.trans (min_le_left _ _))
  simpa only [hηdir] using hh


/-- Preserve the original outer-domain signature by projecting the same
origin-centered comparison targets (`app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian`). -/
theorem exists_retained_normalized_cell_geometry_and_rawAdjoint_with_detector_domain_with_outer_domain {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρc Rc M τlead : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τlead) (hτR : τlead ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τlead))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {O : Set (Euclidean n)} (hO : IsOpen O) (hkO : NormedSpace.normalize k ∈ O)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    ∃ r a r' a' : ℝ, ∃ (_hr : 0 < r) (_ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a'),
      4 * a' < 1 / 2 ∧ 6 * a < cap ∧
      coefficientDomain z₀ r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
      6 * a < T.family.radius ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ hηb : ηb ≠ 0,
      MapsTo parameter (carrierSupport z₀ (r := a')) (parameterInterior P.radius) ∧
      (∀ z ∈ parameter '' carrierSupport z₀ (r := a'), ∀ θ ∈ closedDirections ηb r',
        NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      (∀ detector : Euclidean (n - 1) → ℂ,
        (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections ηb r') →
        ∀ z ∈ parameter '' carrierSupport z₀ (r := a'),
          ∀ θ ∈ Sampling.detectorDirectionSupport detector,
            NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      ∃ δ > (0 : ℝ),
    (∃ (D : CoefficientNormCharts n) (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      (ρ τ : ℝ) (W Bi : Set (InputVariables n)) (It : Set ℝ)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (ε gap : ℝ)
      (Qc Ωi : Set (Variables n × Euclidean 2)),
      0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ (ball (0 : Euclidean n) R ×ˢ V) ∩ coefficientDomain z₀ r (6 * a) ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (CarrierVariation.FamilyInputs.WideDensity.densityEndpoint side)
        W D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) ∧ 0 < gap ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = 1 / 4) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry T Q z₀ ηb r a ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi))) ∧
    ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ hcell : 4 * a' < 1 / 2,
      supportedChart (n := n) z₀ a' ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a') (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
        ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  obtain ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hparameter, hdirections, hdetector, δ, hδ, hgeometry, hraw⟩ :=
    exists_retained_normalized_cell_geometry_and_rawAdjoint_with_origin_targets
      H hP T hUH hbounded hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans
      hR hRphysical hRU hV hVP hflow hz₀ hzV hk hinc hd hO hkO hcap
  refine ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hparameter, hdirections, hdetector, δ, hδ, ?_, hraw⟩
  obtain ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
    _horigin, _hcompact, _hcone, hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD, hrest⟩ := hgeometry
  exact ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
    hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD, hrest⟩

/-- Project the original sampling and raw-adjoint statement from its same
outer-domain-retaining selection (`app:ch_background:defn:bg-row`,
`app:ch_background:prop:bg-adjoint`). -/
theorem exists_retained_normalized_cell_geometry_and_rawAdjoint_with_detector_domain {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρc Rc M τlead : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τlead) (hτR : τlead ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τlead))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {O : Set (Euclidean n)} (hO : IsOpen O) (hkO : NormedSpace.normalize k ∈ O)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    ∃ r a r' a' : ℝ, ∃ (_hr : 0 < r) (_ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a'),
      4 * a' < 1 / 2 ∧ 6 * a < cap ∧
      coefficientDomain z₀ r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
      6 * a < T.family.radius ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ hηb : ηb ≠ 0,
      MapsTo parameter (carrierSupport z₀ (r := a')) (parameterInterior P.radius) ∧
      (∀ z ∈ parameter '' carrierSupport z₀ (r := a'), ∀ θ ∈ closedDirections ηb r',
        NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      (∀ detector : Euclidean (n - 1) → ℂ,
        (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections ηb r') →
        ∀ z ∈ parameter '' carrierSupport z₀ (r := a'),
          ∀ θ ∈ Sampling.detectorDirectionSupport detector,
            NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
      ∃ δ > (0 : ℝ),
    (∃ (D : CoefficientNormCharts n) (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      (ρ τ : ℝ) (W Bi : Set (InputVariables n)) (It : Set ℝ)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (ε gap : ℝ)
      (Qc Ωi : Set (Variables n × Euclidean 2)),
      0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (CarrierVariation.FamilyInputs.WideDensity.densityEndpoint side)
        W D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) ∧ 0 < gap ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = 1 / 4) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry T Q z₀ ηb r a ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi))) ∧
    ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ hcell : 4 * a' < 1 / 2,
      supportedChart (n := n) z₀ a' ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a') (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
        ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  obtain ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hparameter, hdirections, hdetector, δ, hδ, hgeometry, hraw⟩ :=
    exists_retained_normalized_cell_geometry_and_rawAdjoint_with_detector_domain_with_outer_domain
      H hP T hUH hbounded hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans
      hR hRphysical hRU hV hVP hflow hz₀ hzV hk hinc hd hO hkO hcap
  refine ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hparameter, hdirections, hdetector, δ, hδ, ?_, hraw⟩
  obtain ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
    hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD, hrest⟩ := hgeometry
  exact ⟨D, p₀, q₀, ρ, τ, W, Bi, It, A, ε, gap, Qc, Ωi,
    hρ, hτ, hW, hKiW, hBi, hWBi, hBiDom, hD.trans inter_subset_left, hrest⟩

/-- Construct primitive comparison geometry and all raw-adjoint and initial
density estimates on one local normalized source family. The exact same
spatial/angular masks carry the current/frozen conic identities and literal
adjoint representation, with one cutoff and all constants before source scale.
The source scalar remains exactly `σ`, and carrier measure and both quadratures
are unchanged. The original supplied cell and seed are retained; no operator
bound, adjoint regularity or normal-gap estimate is a premise. Consumers:
the finite normalized row, `PositiveBackground.SourceInverse.hrawReg/hraw`,
and the same-family reflected-normal construction
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_normalized_cell_geometry_and_rawAdjoint {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρc Rc M τlead : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τlead) (hτR : τlead ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (FlowConstruction.outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τlead))
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hzV : (z₀ 0, spectatorCenter z₀) ∈ V)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    ∃ r a r' a' : ℝ, ∃ (_hr : 0 < r) (_ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a'),
      4 * a' < 1 / 2 ∧ 6 * a < cap ∧
      coefficientDomain z₀ r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
      6 * a < T.family.radius ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ hηb : ηb ≠ 0, ∃ δ > (0 : ℝ),
    (∃ (D : CoefficientNormCharts n) (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      (ρ τ : ℝ) (W Bi : Set (InputVariables n)) (It : Set ℝ)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (ε gap : ℝ)
      (Qc Ωi : Set (Variables n × Euclidean 2)),
      0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
      Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
      (∀ p ∈ closedBall p₀ ρ, D.Contains p) ∧
      (tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport z₀ (r := a') ⊆ D.field.carrier) ∧
      IsOpen It ∧ Icc (0 : ℝ) 1 ⊆ It ∧
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) ∧
      (∀ side, MapsTo (CarrierVariation.FamilyInputs.WideDensity.densityEndpoint side)
        W D.field.carrier) ∧
      0 < ε ∧ (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) ∧ 0 < gap ∧
      IsCompact Qc ∧ IsOpen Ωi ∧ Qc ⊆ Ωi ∧
      (∀ q ∈ Qc, ‖q.1.2.2‖ = 1 / 4) ∧ (∀ q ∈ Ωi, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ωi ↔ q ∈ Ωi) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        (RetainedSpectralGeometry T Q z₀ ηb r a ∧
        closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
        MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
          (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
        (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (transportPosition T Q) p) ∧
        (closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
            symbolDomain T Q z₀ ηb r (6 * a)) ∧
        (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
        (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
          ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)) ∧
      (let u := symbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q)) W ∧
      EqOn (symbolJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (transportPosition T Q)) W ∧
      InjOn (augmentedTransportGradient (transportPosition T Q)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (transportPosition T Q) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (transportPosition T Q) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (transportPosition T Q) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (transportPosition T Q) p) = p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi)) ∧
      (let u := frozenSymbolInverse T Q z₀ ηb r (6 * a)
      Ωi ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
      ContDiffOn ℝ ∞ u Ωi ∧ MapsTo (inverseCoordinates u) Qc (closedBall p₀ ρ) ∧
      MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius (1 / 4) q)) Ωi (closedBall p₀ ρ) ∧
      (∀ q ∈ Ωi, transportAveragedGradient (normalizedTransportPosition T Q 0)
        (inverseCoordinates u q) = q.1.2.2) ∧
      (∀ p ∈ (closedBall p₀ ρ), ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0) p) ∧
      ContDiffOn ℝ ∞ (transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q 0)) W ∧
      EqOn (frozenKernelJacobian T Q)
        (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)) W ∧
      InjOn (augmentedTransportGradient (normalizedTransportPosition T Q 0)) (closedBall p₀ ρ) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
      (∀ p ∈ conicMaskSupport z₀ ηb r' a',
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ (closedBall p₀ ρ) ∧
        transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0 ∧
        normalizeOutputRadius (1 / 4) (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) ∈ Qc ∧
        scaleInput ((1 / 4) / ‖transportAveragedGradient (normalizedTransportPosition T Q 0) p‖) p ∈ (closedBall p₀ ρ) ∧
        inverseCoordinates u (augmentedTransportGradient (normalizedTransportPosition T Q 0) p) = p) ∧
      (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') ∩ {q | q.1.2.2 ≠ 0} ⊆ Ωi))) ∧
    ∃ χinitial : ContDiffBump (0 : CarrierVariable n),
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ hcell : 4 * a' < 1 / 2,
      supportedChart (n := n) z₀ a' ⊆ ball (0 : Euclidean n) R ×ˢ V ∧
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.2, normalizedTransportPosition T c₀.Q σ p))
        (supportedChart z₀ a') (interior {q | χinitial q = 1}) ∧
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency σ
      (∀ cσ : FlowConstruction.Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρc)
        ((0 : Euclidean (n - 1)), zCell) Rc M τlead row col (sourceDilation H.map σ),
        carrierKernel (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
          (fun _ ↦ σ) ha' hcell (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency) = carrierKernel d) ∧
      ∃ A : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ w, A.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) ∧
        (∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) → B = A) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (A.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Cbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∃ hraw : ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          MemRawSobolev s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)),
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) s,
          rawSobolevNorm s ((carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            (2 * Cbound s) * (‖w‖ + ‖PeriodicSobolevSpace.toL2 s w‖)) ∧
        ∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (Euclidean n) (s + 1),
          let f := (carrierChannel A).adjoint (PeriodicSobolevSpace.toL2 (s + 1) w)
          let hf := (hraw (s + 1) w).mono (by omega : 1 ≤ s + 1)
          MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ∧
          MemPhysicalSobolev s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (densityUncut z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) ∧
          physicalSobolevNorm s (physicalComplexifyL2
            (density z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1 χinitial f hf)) ≤
              Lbound s * (‖w‖ + ‖PeriodicSobolevSpace.toL2 (s + 1) w‖) := by
  obtain ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, _, _, _, hrest⟩ :=
    exists_retained_normalized_cell_geometry_and_rawAdjoint_with_detector_domain
      H hP T hUH hbounded hΩ hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans
      hR hRphysical hRU hV hVP hflow hz₀ hzV hk hinc hd isOpen_univ (mem_univ _) hcap
  exact ⟨t, ht, htnorm, hdir, hηdir, r, a, r', a', hr, ha, hr', ha',
    hcell, hacap, houter, hrr, haa, har', haR, hηb, hrest⟩

end JanetCartan.ContinuumRow.NormalizedSelection
