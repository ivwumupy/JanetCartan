module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSeedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSelectedBalls
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSeedCommonCone
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.CanonicalSourceControl
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization

/-!
# Genuine zero-density normals for the original seed and positive anchor

Apply the existing weighted realization to the original seed's literal kernel,
using the selected geometry of one positive member of the same family. The
original scalar domain, divided footpoints, masks and measurement are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry
open CarrierVariation.FamilyInputs.PositiveReference CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2 SourceDensityLimitRealization

/-- Construct both literal zero-density carriers for the supplied original
seed using the geometry of one admitted positive source. The existing weighted
realization discharges all boundedness, test and adjoint conclusions. Exact
kernel transfer and full-mask common-cone equality identify the normal with
any valid consumer witnesses. This applies the producer on the unchanged
`L/8`, `μ+14` density class and keeps the divided-footpoint weight distinct
from the origin weight. Constants precede density. Consumer: the zero normal
in `exists_selected_source_family_normal_control`, then actual normal coercivity
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`). -/
theorem exists_retained_seed_zero_density_realization_of_source
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow : Set (Euclidean n × Euclidean 3)} (hΩflow : IsOpen Ωflow)
    {zCell : Euclidean 3} {ρc Rc Bflow τflow : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ωflow)
    (hΩpatch : Ωflow ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τflow) (hτR : τflow ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {L Mc R : ℝ} (hL : 0 < L) (hMc : 0 < Mc) (hR : 0 < R)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (Qanchor : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {anchor : ℝ} (hanchor : 0 < anchor) (hanchor1 : anchor ≤ 1)
    (hanchorFrame : Qanchor.1 = ProjectedStressFrame.projectedStress (sourceDilation F anchor))
    (hgeometry : RetainedSpectralGeometry T Qanchor zRoot ηb r a)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτout : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall p₀ ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    (hKInput : K ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Qanchor zRoot ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Qanchor zRoot ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Qanchor) ''
        conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τ)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegI : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
    (hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
    (hgap : ∀ p ∈ closedBall p₀ ρ,
      ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Qanchor 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Qanchor 0) p)
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport zRoot (r := a') ⊆ D.field.carrier)
    {Ωcommon : Set (Variables n × Euclidean 2)}
    (hcommon : Ωcommon ⊆ frozenSymbolDomain T Qanchor zRoot ηb r (6 * a))
    (hcommonBuffer : closure (augmentedTransportGradient (normalizedTransportPosition T Qanchor 0) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆ Ωcommon) :
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let e₀ := normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
      ha' hcell angular FixedCutoffs.highFrequency 0
    let a₀ := coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1)
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T seed.Q 0)
    let u := frozenSymbolInverse T seed.Q zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    ∃ M ≥ (0 : ℝ), ∃ B > (0 : ℝ),
    ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (2 * (n + 1) + 14) v ≤ 1 →
    ∀ t : Bool,
    let w := fun p : Euclidean n × CarrierParameter ↦ Real.sqrt (1 + v
      (if t then sourceDensityFootpointExtension T seed.inverse (0, p) else (0, parameter p.2)))
    let e := weightNormal e₀ w
    let d := {a₀ with normal := fun p ↦ w p • a₀.normal p}
    let b := fullReflectedMatrixAmplitude d J u Ωcommon S
    ∃ hb : ContDiff ℝ ∞ (Function.uncurry b),
    ∃ hA : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1) + 1) B,
    ∃ hs : ∀ ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b ξ z i j),
    ∃ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖Vop‖ ≤ M ∧ ‖Vop.adjoint‖ ≤ M ∧
      (∀ f : carrierInitialTestSpace n,
        Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) ∧
      (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral e f) 2 (carrierMeasure n) ∧
        Vop.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral e f) ∧
      (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → Wop = Vop) ∧
      (t = false → ∀ Vfrozen : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          Vfrozen (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral
            (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun q ↦ Real.sqrt (1 + v q))
              ha' hcell angular FixedCutoffs.highFrequency 0) f.val) → Vfrozen = Vop) ∧
      carrierChannel Vop ∘L (carrierChannel Vop).adjoint = realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator (by have := row.isLt; omega) (4 * a') b hb hs B
          (fun i j ξ is his ↦ hA i j ξ is (by omega)))) ∧
      ∀ (Rbox Bconsumer : ℝ) (hbc : ContDiff ℝ ∞ (Function.uncurry b))
        (hsc : ∀ ξ i j, SupportedInCenteredBox Rbox (fun z ↦ b ξ z i j))
        (hBc : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) Bconsumer),
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint = realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator (by have := row.isLt; omega) Rbox b hbc hsc Bconsumer hBc)) := by
  classical
  intro angular e₀ a₀ J u S
  have hn : 0 < n := by have := row.isLt; omega
  have ha : 0 < a := ha'.trans_le haa
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hdom := frozenSymbolDomain_eq_of_source_dilation T seed.Q Qanchor hF hrank hphysical
    seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP (ηb := ηb) hr hgeometry.1 hgeometry.2.1
  have hinv := frozenSymbolInverse_eq_of_source_dilation T seed.Q Qanchor hF hrank hphysical
    seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP hηb hr hgeometry
  obtain ⟨haug, hdiff, hJac⟩ := source_frozen_transport_geometry_eq T seed.Q Qanchor hF hrank hphysical
    seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP (ηb := ηb) hr hgeometry.1 hgeometry.2.1
  obtain ⟨hout0, hrange0, hshell0⟩ := seed_frozen_output_geometry_of_source T seed.Q Qanchor hF hrank
    hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP hηb hr hr' ha' hrr haa
    hgeometry hτout hquarter houtput hrange hshell
  obtain ⟨charts, symbols, hsymbols⟩ := exists_seed_frozen_kernel_inputs_of_source T seed.Q Qanchor
    hF hrank hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP hηb hr hgeometry
    row col seed.forward seed.inverse hr' ha' hrr haa har' hcell
  obtain ⟨Cfreq, hCfreq, hcompare⟩ := exists_seed_frozen_frequency_comparison_of_source
    T seed.Q Qanchor hF hrank hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame
    hP hηb hr hgeometry
  have hAmplitude := seed_zero_weighted_fullAmplitudes_eq_common_cone_of_source T seed.Q Qanchor
    hF hrank hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP hηb hr hgeometry
    row col seed.forward seed.inverse hr' ha' hrr haa har' hcell hcommon hcommonBuffer
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, hcJ, hVi, hLi, hf, hInv, hcone, _hslice⟩ := hgeometry
  let Z := normalizedTransportPosition T seed.Q 0
  let Ω := frozenSymbolDomain T seed.Q zRoot ηb r (6 * a)
  let Wi := frozenInputDomain zRoot ηb r (6 * a)
  have hopen : IsOpen Ω := by
    dsimp only [Ω]
    rw [← hdom]
    exact frozenSymbolDomain_open T Qanchor hηb hr hInv hcone hVi hLi
  have hu : ContDiffOn ℝ ∞ u Ω := by
    dsimp only [u, Ω]
    rw [← hinv, ← hdom]
    exact frozenSymbolInverse_smooth T Qanchor hηb hr hInv hcone hLi
  have hmap : MapsTo (inverseCoordinates u) Ω Wi := by
    dsimp only [u, Ω, Wi]
    rw [← hinv, ← hdom]
    exact frozenSymbolInverse_maps T Qanchor hηb hr hInv hcone
  have hright : ∀ p ∈ Ω, transportAveragedGradient Z (inverseCoordinates u p) = p.1.2.2 := by
    intro p hp
    have hh := congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) (haug (hmap hp))
    change transportAveragedGradient (normalizedTransportPosition T Qanchor 0)
      (inverseCoordinates u p) = transportAveragedGradient Z (inverseCoordinates u p) at hh
    rw [← hh]
    dsimp only [u]
    rw [← hinv]
    exact frozenTransportGradient_inverse T Qanchor hP hηb hr har hcarrier hInv hcone
      (by rwa [hdom])
  have hJsmooth : ContDiffOn ℝ ∞ J Wi :=
    (frozenJacobian_smooth T Qanchor hP hηb hr har hcarrier hInv hcone hf hcJ).congr
      (fun p hp ↦ (hJac hp).symm)
  have hJpos : ∀ p ∈ Wi, 0 < J p := fun p hp ↦
    (frozenJacobian_pos T Qanchor hP hηb hr har hcarrier hInv hcone hf hcJ hp).trans_eq (hJac hp)
  have hWinput : W ⊆ Wi := (hWK.trans hKInput).trans
    (symbolInputDomain_subset_frozenInputDomain zRoot ηb r (by positivity))
  have hballInput := hball.trans hWinput
  have hJscale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p) := by
    intro t ht p hp
    have hi := hmap hp
    have hit : scaleInput t (inverseCoordinates u p) ∈ Wi :=
      ⟨hi.1, radialScale_mem_supportedCone hi.2 ht⟩
    calc
      _ = transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (normalizedTransportPosition T Qanchor 0) (scaleInput t (inverseCoordinates u p)) := (hJac hit).symm
      _ = t * transportAbsoluteJacobian (adaptedSliceCoordinates T)
          (normalizedTransportPosition T Qanchor 0) (inverseCoordinates u p) :=
        frozenJacobian_scaling T Qanchor hP hηb hr har hcarrier hf hInv hcone hi ht
      _ = _ := congrArg (fun z ↦ t * z) (hJac hi)
  have huscale : ∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
      u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2) := by
    intro t ht p hp
    dsimp only [u]
    rw [← hinv]
    exact frozenSymbolInverse_smul T Qanchor hηb hr hInv hcone (by rwa [hdom]) ht
  have hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ 2 * ‖p.1.2.2‖ := by
    intro p hp
    dsimp only [u]
    rw [← hinv]
    exact frozenSymbolInverse_norm_le_two T Qanchor hηb hr hInv hcone (by rwa [hdom])
  have hmaskInput : conicMaskSupport zRoot ηb r' a' ⊆ Wi := by
    intro p hp
    exact conicMaskSupport_subset hηb hr ha (by linarith only [har, ha])
      (conicMaskSupport_mono zRoot ηb hrr haa (originInput_mem_conicMaskSupport ha'.le hp))
  have hpunct : closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ∩
      {p | p.1.2.2 ≠ 0} ⊆ Ω := by
    dsimp only [Ω, Z]
    rw [← (haug.mono hmaskInput).image_eq, ← hdom]
    exact frozenRefinedMaskImage_punctured_buffer T Qanchor hP hηb hr ha har hcarrier hf hcone hrr haa
  obtain ⟨hY, _, hzero, hparam, _⟩ := exists_retained_chart_source_primitive_convergence_on_outputCylinder
    hP T hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
      hR hRT hRU hV hVP hflow D (D.field.ball_subset.trans hD) a' ha' hcell angular FixedCutoffs.highFrequency
  have hmaps := fun p hp ↦ seed.small_subset ((outputCylinder_spec hRc hτ).2 (hflow (x := p) hp))
  obtain ⟨_, hscalar, _, _, _, _, _, _⟩ := seed.scalar_spec hτ (fun _ ↦ 1)
    contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have hb := hscalar.comp
    (contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)).contDiffOn hmaps
  have hsource : ∀ σ ∈ Ioc (0 : ℝ) 1,
      MapsTo (densityFootpoint T (sourceTransportFlow seed.inverse σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
    intro σ hσ p hp
    apply sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc
      seed hforward (hflow hp) (hlabel p hp) _ hσ.1 hσ.2
    change |(adaptedCoordinates T.data.adapted p.1).1| < L / (64 * Mc)
    rw [adaptedCoordinates_apply]
    have ht := abs_real_inner_le_norm T.data.adapted.normal p.1
    rw [T.data.adapted.normal_unit, one_mul] at ht
    exact (ht.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le hRtime
  have hchartR : 4 * a' < R := by
    have hx : EuclideanSpace.single row (5 * a) ∈ ball (0 : Euclidean n) (6 * a) := by
      rw [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith only [ha]
    have hh := (houter (show (EuclideanSpace.single row (5 * a), (zRoot 0, spectatorCenter zRoot)) ∈
      coefficientDomain zRoot r (6 * a) from ⟨hx, mem_ball_self hr, mem_ball_self (by positivity)⟩)).1
    rw [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)] at hh
    linarith only [hh, haa, ha']
  let E := ball (0 : Euclidean n) R ×ˢ V
  let D' : CoefficientNormCharts n := {D with field := {
    D.field with region := E
                 isOpen_region := isOpen_ball.prod hV
                 ball_subset := D.field.ball_subset.trans hD }}
  let physicalPositions := {p : Variables n × Euclidean 2 |
    p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
  let Ui := Wi ∩ {p : InputVariables n | p.1.1 ∈ ball 0 R ∧ p.1.2 ∈ ball 0 R}
  have hlabelV {p : InputVariables n} (hp : p ∈ Wi) : p.2.1 ∈ V :=
    (houter (show ((0 : Euclidean n), p.2.1) ∈ coefficientDomain zRoot r (6 * a) from
      ⟨mem_ball_self (by positivity), hp.2.1, hp.1.1⟩)).2
  have hend : ∀ side, MapsTo (densityEndpoint side) Ui E := by
    intro side p hp
    cases side
    · exact ⟨hp.2.1, hlabelV hp.1⟩
    · exact ⟨hp.2.2, hlabelV hp.1⟩
  have hopenLocal : IsOpen (Ω ∩ physicalPositions) :=
    hopen.inter ((isOpen_ball.preimage continuous_fst.fst).inter
      (isOpen_ball.preimage continuous_fst.snd.fst))
  have houtputLocal : closedBall q₀ τ ⊆ Ω ∩ physicalPositions := by
    intro p hp
    have hp' := closedBall_subset_closedBall (by linarith only [hτout] : τ ≤ 2 * τ) hp
    have hf := hfoot _ (hrange0 hp')
    exact ⟨hout0 hp', (hD (D.field.ball_subset hf.2.2.2.2.1)).1,
      (hD (D.field.ball_subset hf.2.2.2.2.2)).1⟩
  have hpunctLocal : closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') ∩
      {p | p.1.2.2 ≠ 0} ⊆ Ω ∩ physicalPositions := by
    intro p hp
    have hxy := conicMaskImage_position_support Z zRoot ηb r' a' hp.1
    exact ⟨hpunct hp, closedBall_subset_ball hchartR hxy.1, closedBall_subset_ball hchartR hxy.2⟩
  obtain ⟨M, hM, B, hB, _Ccommon, _hCcommon, hrealize⟩ :=
    exists_source_zero_density_limit_realization T seed.Q F row col seed.forward seed.inverse
      ha' hcell angular (angularMask_smooth ..) hP seed.frame_eq hF.contDiffOn hi hrank
      hR hRT hRU (by linarith only [hchartR, ha']) hV hVP hb hY hzero hparam hL zero_lt_one hsource
      D' Subset.rfl p₀ q₀ hρ hτout hW hball hK hWK hopenLocal houtputLocal hIt hIIt
      (fun t ht p hp ↦ hD (hsegI t ht hp)) hseg A hδ hε hfreq hfoot
      (Cupper := 2) (by norm_num) hquarter (by norm_num) (by norm_num) (isCompact_closedBall ..) u
      hopenLocal Subset.rfl (hu.mono inter_subset_left)
      (hrange0.mono_left (closedBall_subset_closedBall (by linarith only [hτout])))
      (fun p hp ↦ by rw [← hdiff (hballInput hp)]; exact hgap p hp)
      (fun p hp ↦ hright p hp.1) (fun p hp ↦ (hJpos p (hWinput hp)).ne')
      (fun p hp ↦ (hJlow p hp).trans_eq (hJac (hballInput hp)))
      (hJsmooth.mono inter_subset_left) (fun p hp ↦ (hJpos p hp.1).ne')
      (fun p hp ↦ hp.1.2.2.1) hend (fun p hp ↦ ⟨hmap hp.1, hp.2⟩)
      (fun p hp hx hy hang ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.1.2.2.1 hx hy hang)
      hpunctLocal (fun x hx v _ hp ↦ hshell0 x hx v hp)
      (fun t ht p ↦ by
        change ((scaleFrequency t p.1, p.2) ∈ Ω ∧ _) ↔ (p ∈ Ω ∧ _)
        rw [frozenSymbolDomain_smul_iff T seed.Q zRoot ηb r (6 * a) ht p]
        rfl)
      (fun t ht p hp ↦ huscale t ht p hp.1) (fun t ht p hp ↦ hJscale t ht p hp.1)
      (fun p hp ↦ hupper p hp.1) (carrierSupport zRoot (r := a')) (carrierSupport_compact zRoot)
      (fun z hz η ↦ angularMask_zero_outside zRoot (NormedSpace.normalize ηb) ha'
        (angularWidth_spec hηb hr').1 hz η) hsupportD hchartR
      charts symbols
      (fun q hq x hx y hy ↦ (hsymbols q hq x hx y hy).1)
      (fun q hq x hx y hy ↦ (hsymbols q hq x hx y hy).2.1)
      (fun q hq x hx y hy ↦ (hsymbols q hq x hx y hy).2.2.1)
      (fun q hq x hx y hy ↦ (hsymbols q hq x hx y hy).2.2.2.1)
      (fun q hq x hx y hy ↦ (hsymbols q hq x hx y hy).2.2.2.2.1)
      (fun q hq x hx y hy ↦ by rw [(hsymbols q hq x hx y hy).2.2.2.2.2.1]; exact inter_subset_left)
      Cfreq hCfreq.le (fun p hp ↦ hcompare p hp.1)
  refine ⟨M, hM, B, hB, ?_⟩
  intro v hv hpos hinterval hvnorm t w e d b
  obtain ⟨hbOld, hAOld, hsOld, Vop, hV, hAdj, htest, _hsupp, huniq, hadj, hfrozen, hnormal, _hcommon⟩ :=
    hrealize v hv hpos hinterval hvnorm t
  have heq : fullReflectedMatrixAmplitude d J u Ω S = b := (hAmplitude w S).2.2
  have hbNew : ContDiff ℝ ∞ (Function.uncurry b) := heq ▸ hbOld
  have hANew : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1) + 1) B := heq ▸ hAOld
  have hsNew : ∀ ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b ξ z i j) := heq ▸ hsOld
  have hnNew := realized_normal_eq_of_amplitude_witnesses hn (4 * a') (4 * a')
    _ b hbOld hbNew hsOld hsNew B B (fun i j ξ is his ↦ hAOld i j ξ is (by omega))
    (fun i j ξ is his ↦ hANew i j ξ is (by omega)) heq Vop hnormal
  refine ⟨hbNew, hANew, hsNew, Vop, hV, hAdj, htest, hadj, huniq, hfrozen, hnNew, ?_⟩
  intro Rbox Bconsumer hbc hsc hBc
  exact realized_normal_eq_of_amplitude_witnesses hn (4 * a') Rbox b b hbNew hbc hsNew hsc B Bconsumer
    (fun i j ξ is his ↦ hANew i j ξ is (by omega)) hBc rfl Vop hnNew

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
