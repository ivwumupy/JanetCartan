module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCarrier

/-!
# Literal density carriers on the retained history charts

Construct the original nonconstant-density carrier on a supplied current chart
and the retained conic geometry. Smoothness follows from the scalar equation,
actual inverse ODE labels and the principal-normal formula. Finite primitive
budgets then give the bounded extension, literal adjoint and reflected normal.

The existence budgets here may depend on the individual density and chart.
Uniform normal differences are supplied separately by the retained full-amplitude
comparison. The common geometry is the corresponding projection of
`NormalizedSelection.exists_finite_incidence_comparison_inputs`.
Consumer: the actual history normal comparison in `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric MeasureTheory
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

/-- The actual density carrier has smooth fields on the original coefficient
product. Its nonconstant scalar is evaluated at the retained inverse ODE label;
the unit scalar equation and the canonical normal formula prove regularity
(`app:ch_background:eq:bg-T`, `app:ch_waves:thm:leading`). -/
theorem retained_chart_density_fields_smooth
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {zCell : Euclidean 3} {Rc B τ L Mc R σ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (current : Chart T Ω K ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (hRc : 0 < Rc) (hτ : 0 < τ) (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 current.forward ≤ Mc)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hpatch : ball (0 : Euclidean n) R ×ˢ V ⊆
      (U ∩ ball 0 T.physicalRadius) ×ˢ (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)))
    (hpos : ∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) :
    ContDiffOn ℝ ∞ (Function.uncurry (normalField T current.Q F row col
      current.forward current.inverse (fun q ↦ positiveDensityAmplitude σ (v q))))
      (ball (0 : Euclidean n) R ×ˢ V) ∧
    ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2)))
      (ball (0 : Euclidean n) R ×ˢ V) := by
  let E := ball (0 : Euclidean n) R ×ˢ V
  have hE : IsOpen E := isOpen_ball.prod hV
  have hmaps : MapsTo (densityCoordinates T) E current.D :=
    hflow.mono_right ((outputCylinder_spec hRc hτ).2.trans current.small_subset)
  have hY : ContDiffOn ℝ ∞ (densityFootpoint T current.inverse) E :=
    current.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn hmaps
  have hrange : MapsTo (densityFootpoint T current.inverse) E
      (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) := by
    intro p hp
    have ht : |(densityCoordinates T p).1| < L / (64 * Mc) := by
      change |(adaptedCoordinates T.data.adapted p.1).1| < _
      rw [adaptedCoordinates_apply]
      have hh := abs_real_inner_le_norm T.data.adapted.normal p.1
      rw [T.data.adapted.normal_unit, one_mul] at hh
      exact (hh.trans_lt (mem_ball_zero_iff.mp hp.1)).trans_le hRtime
    have hh := sourceDensityFootpoint_mem_original_ball_of_forward_cNorm T hL hRc hτ hMc
      current hforward (hflow hp) (hlabel p hp) ht zero_lt_one le_rfl
    have hrange16 : densityFootpoint T current.inverse p ∈
        ball ((0 : Euclidean (n - 1)), zCell) (L / 16) := by
      simpa only [densityFootpoint, NormalizedBackground.SourceGeometry.sourceTransportFlow,
        transportCoordinateDilation,
        transportLabelDilation,
        inv_one, one_mul, one_smul, Prod.mk.eta] using hh
    exact ball_subset_ball (by linarith only [hL] : L / 16 ≤ L / 4) hrange16
  have hweight : ContDiffOn ℝ ∞
      (fun p ↦ Real.sqrt (1 + v (densityFootpoint T current.inverse p))) E :=
    (contDiffOn_const.add (hv.comp hY hrange)).sqrt (fun p hp ↦ ne_of_gt (hpos _ (hrange hp)))
  have hpull : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) :=
    contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hξmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)) E
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :=
    fun p hp ↦ ⟨(hpatch hp).1.2, fun j ↦ ((hpatch hp).2 j).trans (by linarith only [hP.1])⟩
  have hξ := (T.carrierGradient_smooth hP current.Q).comp hpull.contDiffOn hξmaps
  have hq : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2))) E :=
    (quadratic_canonical_smooth T hP current.Q).mono
      (fun p hp ↦ ⟨(hpatch hp).1, fun j ↦ ((hpatch hp).2 j).trans (by linarith only [hP.1])⟩)
  have hb : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T current.Q F row col current.forward current.inverse (fun _ ↦ 1)
        (p.1, parameter p.2) • carrierNullvector T current.Q col (p.1, parameter p.2)) E :=
    (current.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)).2.1.comp
      hpull.contDiffOn hmaps
  have hnormal : ContDiffOn ℝ ∞ (Function.uncurry (normalField T current.Q F row col
      current.forward current.inverse (fun _ ↦ 1))) E := by
    let b := fun p : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T current.Q F row col current.forward current.inverse (fun _ ↦ 1)
        (p.1, parameter p.2) • carrierNullvector T current.Q col (p.1, parameter p.2)
    let ξ := fun p : Euclidean n × CarrierParameter ↦ T.carrierGradient current.Q p.1 (parameter p.2)
    intro p hp
    have hxU : ball (0 : Euclidean n) R ⊆ U := by
      intro x hx
      exact (hpatch (show (x, p.2) ∈ E from ⟨hx, hp.2⟩)).1.1
    have hFU : ContDiffOn ℝ ∞ F (ball (0 : Euclidean n) R) := hF.mono hxU
    have hjet := contDiffOn_jointJet isOpen_ball hV hFU hb hξ
    have hFp : ContDiffAt ℝ 2 F p.1 :=
      (hF.contDiffAt (hU.mem_nhds (hpatch hp).1.1)).of_le (by simp)
    have hri : Set.range (secondJetNormalMap (secondJet F p.1)) =
        ((LinearMap.range (fderiv ℝ F p.1).toLinearMap)ᗮ : Set (Euclidean N)) := by
      rw [secondJetNormalMap_eq_of_contDiffAt hFp (hi _ (hpatch hp).1.1)]
      exact hrank _ (hpatch hp).1.1
    have hcoef := contDiffAt_principalNormalValue (q := jointJet F b ξ p)
      (hi _ (hpatch hp).1.1) hri
    have he := (jointJet_fields_eventuallyEq ξ isOpen_ball hV hFU hb
      (fun x hx ↦ hi x (hxU hx)) (fun x hx ↦ hrank x (hxU hx)) hp).1
    exact ((hcoef.comp p (hjet.contDiffAt (hE.mem_nhds hp))).congr_of_eventuallyEq
      he.symm).contDiffWithinAt
  refine ⟨?_, hq⟩
  have hsm : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (σ * Real.sqrt (1 + v (densityFootpoint T current.inverse p))) •
        normalField T current.Q F row col current.forward current.inverse (fun _ ↦ 1) p.1 p.2) E :=
    (contDiffOn_const.mul hweight).smul hnormal
  apply hsm.congr
  intro p hp
  simpa only [Function.uncurry, one_mul, positiveDensityAmplitude] using
    normalField_initial_mul T current.Q F row col current.forward current.inverse
      (fun _ ↦ 1) (fun q ↦ positiveDensityAmplitude σ (v q)) p.1 p.2


/-- Construct the carrier and its literal normal on the supplied retained chart
and unchanged masks, for the original positive density. Primitive budgets are
chosen from its actual smooth fields, without any forward/adjoint-output premise
(`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_retained_chart_density_normal
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow Kflow : Set (Euclidean n × Euclidean 3)}
    {zCell : Euclidean 3} {Rc Bflow τflow L Mc R σ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (current : Chart T Ωflow Kflow ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (hRc : 0 < Rc) (hτflow : 0 < τflow) (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 current.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (zRoot : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (haR : 6 * a < T.family.radius)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hDouter : D.field.region ⊆ coefficientDomain zRoot r (6 * a))
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport zRoot (r := a') ⊆ D.field.carrier)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρi τi : ℝ} (hρi : 0 < ρi) (hτi : 0 < τi)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρi ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρi, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap : ℝ} (hε : 0 < ε) (hgap : 0 < gap)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    (hspectral : RetainedSpectralGeometry T current.Q zRoot ηb r a)
    (houtput : closedBall q₀ (2 * τi) ⊆ symbolDomain T current.Q zRoot ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T current.Q zRoot ηb r (6 * a)))
      (closedBall q₀ (2 * τi)) (closedBall p₀ ρi))
    (hgapA : ∀ p ∈ closedBall p₀ ρi, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (transportPosition T current.Q)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hJacLow : ∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (transportPosition T current.Q) p)
    (hpunctured : closure (augmentedTransportGradient (transportPosition T current.Q) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
        symbolDomain T current.Q zRoot ηb r (6 * a))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T current.Q) ''
        conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τi)
    (hupper : ∀ p ∈ symbolDomain T current.Q zRoot ηb r (6 * a),
      ‖(symbolInverse T current.Q zRoot ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)))
    (hpos : ∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) :
    let e := data T current.Q F row col current.forward current.inverse
      (fun q ↦ positiveDensityAmplitude σ (v q)) ha' hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency
    let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let J := symbolJacobian T current.Q
    let u := symbolInverse T current.Q zRoot ηb r (6 * a)
    let Ωi := symbolDomain T current.Q zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    ∃ Cnorm > (0 : ℝ), ∃ Cpdo > (0 : ℝ),
    ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
    ∃ hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ωi S)),
    ∃ hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j) (2 * (n + 1) + 1) Cpdo,
    ∃ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      ‖Vop‖ ≤ Cnorm ∧ ‖Vop.adjoint‖ ≤ Cnorm ∧
      (∀ f : carrierInitialTestSpace n,
        Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → Vop f x = 0) ∧
      (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → Wop = Vop) ∧
      (∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
        Vop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
      (realQuadratureChannel Vop).comp (realQuadratureChannel Vop).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator (by have := row.isLt; omega) (4 * a')
            (fullReflectedMatrixAmplitude d J u Ωi S) hb
            (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ωi S (4 * a') hsupport)
            Cpdo (fun i j ξ is his ↦ hA i j ξ is (by omega)))) := by
  classical
  intro e d J u Ωi S
  let E := ball (0 : Euclidean n) R ×ˢ V
  let D' : CoefficientNormCharts n := {D with field := {
    D.field with region := E
                 isOpen_region := isOpen_ball.prod hV
                 ball_subset := D.field.ball_subset.trans hD }}
  let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  let initial := fun q ↦ positiveDensityAmplitude σ (v q)
  let μ := 2 * (n + 1) + 1
  have hpatch : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    fun p hp ↦ ⟨⟨hRU hp.1, ball_subset_ball hRT hp.1⟩, hVP hp.2⟩
  obtain ⟨hν, hq⟩ := retained_chart_density_fields_smooth hP T hF hi hrank current
    hRc hτflow hL hMc hforward hRtime hV hpatch hflow hlabel v hv hpos (σ := σ)
  have hdetreg (i : Fin n) : ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2)) i) E :=
    contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn hq) i
  have hZ : ContDiffOn ℝ ∞ (transportPosition T current.Q) D.field.region :=
    (transportPosition_smooth T current.Q hP).mono (fun p hp ↦
      ⟨ball_subset_ball haR.le (hDouter hp).1, hVP (hD hp).2⟩)
  let Mc₀ := cNorm D.measurement.carrier 1 d.measurement +
    cNorm D.angular.carrier 1 d.angular + cNorm D.high.carrier 1 d.high +
    cNorm D.field.carrier 1 d.normal + cNorm D.field.carrier 1 d.reduced
  let Bc₀ := 1 + cNorm D.measurement.carrier μ d.measurement +
    cNorm D.angular.carrier μ d.angular + cNorm D.high.carrier μ d.high +
    cNorm D.field.carrier μ d.normal + cNorm D.field.carrier μ d.reduced
  have hMc₀ : 0 ≤ Mc₀ := by
    dsimp only [Mc₀]
    linarith only [cNorm_nonneg D.measurement.carrier 1 d.measurement,
      cNorm_nonneg D.angular.carrier 1 d.angular, cNorm_nonneg D.high.carrier 1 d.high,
      cNorm_nonneg D.field.carrier 1 d.normal, cNorm_nonneg D.field.carrier 1 d.reduced]
  have hBc₀ : 1 ≤ Bc₀ := by
    dsimp only [Bc₀]
    linarith only [cNorm_nonneg D.measurement.carrier μ d.measurement,
      cNorm_nonneg D.angular.carrier μ d.angular, cNorm_nonneg D.high.carrier μ d.high,
      cNorm_nonneg D.field.carrier μ d.normal, cNorm_nonneg D.field.carrier μ d.reduced]
  have hred : ContDiffOn ℝ ∞ d.reduced E := by
    dsimp only [d, e]
    rw [coefficientsOfCarrier_data]
    exact PiLp.contDiff_ofLp.comp_contDiffOn hq
  have hc : D'.Controls μ Mc₀ Bc₀ 1 d := by
    constructor
    · refine ⟨(FixedCutoffs.physical ha' 1).contDiff.contDiffOn, ?_, ?_⟩
      · dsimp only [Mc₀]; linarith only [cNorm_nonneg D.angular.carrier 1 d.angular, cNorm_nonneg D.high.carrier 1 d.high,
          cNorm_nonneg D.field.carrier 1 d.normal, cNorm_nonneg D.field.carrier 1 d.reduced]
      · rw [mul_one]; dsimp only [Bc₀]
        linarith only [cNorm_nonneg D.angular.carrier μ d.angular, cNorm_nonneg D.high.carrier μ d.high,
          cNorm_nonneg D.field.carrier μ d.normal, cNorm_nonneg D.field.carrier μ d.reduced]
    · refine ⟨(angularMask_smooth ..).contDiffOn, ?_, ?_⟩
      · dsimp only [Mc₀]; linarith only [cNorm_nonneg D.measurement.carrier 1 d.measurement,
          cNorm_nonneg D.high.carrier 1 d.high, cNorm_nonneg D.field.carrier 1 d.normal, cNorm_nonneg D.field.carrier 1 d.reduced]
      · rw [mul_one]; dsimp only [Bc₀]
        linarith only [cNorm_nonneg D.measurement.carrier μ d.measurement, cNorm_nonneg D.high.carrier μ d.high,
          cNorm_nonneg D.field.carrier μ d.normal, cNorm_nonneg D.field.carrier μ d.reduced]
    · refine ⟨FixedCutoffs.highFrequency_smooth.contDiffOn, ?_, ?_⟩
      · dsimp only [Mc₀]; linarith only [cNorm_nonneg D.measurement.carrier 1 d.measurement,
          cNorm_nonneg D.angular.carrier 1 d.angular, cNorm_nonneg D.field.carrier 1 d.normal, cNorm_nonneg D.field.carrier 1 d.reduced]
      · rw [mul_one]; dsimp only [Bc₀]
        linarith only [cNorm_nonneg D.measurement.carrier μ d.measurement, cNorm_nonneg D.angular.carrier μ d.angular,
          cNorm_nonneg D.field.carrier μ d.normal, cNorm_nonneg D.field.carrier μ d.reduced]
    · refine ⟨hν, ?_, ?_⟩
      · change cNorm D.field.carrier 1 _ ≤ Mc₀
        dsimp only [Mc₀]; linarith only [cNorm_nonneg D.measurement.carrier 1 d.measurement,
          cNorm_nonneg D.angular.carrier 1 d.angular, cNorm_nonneg D.high.carrier 1 d.high, cNorm_nonneg D.field.carrier 1 d.reduced]
      · change 1 + cNorm D.field.carrier μ _ ≤ Bc₀ * 1
        rw [mul_one]; dsimp only [Bc₀]
        linarith only [cNorm_nonneg D.measurement.carrier μ d.measurement, cNorm_nonneg D.angular.carrier μ d.angular,
          cNorm_nonneg D.high.carrier μ d.high, cNorm_nonneg D.field.carrier μ d.reduced]
    · refine ⟨hred, ?_, ?_⟩
      · change cNorm D.field.carrier 1 _ ≤ Mc₀
        dsimp only [Mc₀]; linarith only [cNorm_nonneg D.measurement.carrier 1 d.measurement,
          cNorm_nonneg D.angular.carrier 1 d.angular, cNorm_nonneg D.high.carrier 1 d.high, cNorm_nonneg D.field.carrier 1 d.normal]
      · change 1 + cNorm D.field.carrier μ _ ≤ Bc₀ * 1
        rw [mul_one]; dsimp only [Bc₀]
        linarith only [cNorm_nonneg D.measurement.carrier μ d.measurement, cNorm_nonneg D.angular.carrier μ d.angular,
          cNorm_nonneg D.high.carrier μ d.high, cNorm_nonneg D.field.carrier μ d.normal]
  have hcRaw := hc
  dsimp only [d, e] at hc
  rw [coefficientsOfCarrier_data] at hc
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, hconstruct⟩ :=
    exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρi hτi hW hKiW hBi hWBi
      (O := ball q₀ (2 * τi)) isOpen_ball (closedBall_subset_ball (by linarith))
      D.field.isOpen_region (isCompact_closedBall _ _) D.field.ball_subset
      hIt hIIt hsegT hseg A (cNorm_nonneg D.field.carrier 3 (transportPosition T current.Q)) hMc₀ hBc₀ hgap hε
      (add_nonneg zero_le_one (cNorm_nonneg D.field.carrier (μ + 2) (transportPosition T current.Q)))
      (fun p hp ↦ hfreq p (hWBi (hKiW hp))) D' hfoot
      (Cupper := 2) (ℓ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (S := closedBall (spectatorCenter zRoot) (a' / 2)) (isCompact_closedBall _ _)
      μ (by dsimp [μ]; omega) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
      FixedCutoffs.radialRegularization_smooth FixedCutoffs.radialRegularization_compact
      (fun _ ht ↦ FixedCutoffs.radialRegularization_one ht)
  obtain ⟨houterRadius, hcarrier, G, β, cJ, W₀, L₀, hcJ, hW₀, hL₀W₀,
    hf, hInv, htransverse, hsliceGap⟩ := hspectral
  let Lq := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  have hqM : cNorm D.field.carrier 1 (fun p : Euclidean n × CarrierParameter ↦
      quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2))) ≤
      ‖Lq‖ * Mc₀ := by
    have hbound := InverseEstimates.cNorm_postLinear_le_on
      (isCompact_closedBall D.field.center D.field.radius) 1 Lq
      (fun x hx ↦ (hc.reduced.smooth.contDiffAt
        (D'.field.isOpen_region.mem_nhds (D'.field.ball_subset hx))).of_le (by simp))
    exact hbound.trans (mul_le_mul_of_nonneg_left hc.reduced.low (norm_nonneg _))
  have hang : ContDiff ℝ ∞ (Function.uncurry angular) := angularMask_smooth ..
  have hangular : ∀ z ∉ carrierSupport zRoot (r := a'), ∀ η, angular z η = 0 :=
    fun _ hz η ↦ angularMask_zero_outside zRoot (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz η
  have hkernel := stronglyMeasurable_carrierKernel_of_local_primitives T current.Q
    F row col current.forward current.inverse initial ha' hcell angular
    D.field.isOpen_region hZ.continuousOn (hν.mono hD).continuousOn (hq.mono hD).continuousOn
    hang.continuous hangular (hsupportD.trans D.field.ball_subset)
  let Cmask := cNorm (carrierSupport zRoot (r := a') ×ˢ closedBall (0 : Euclidean (n - 1)) 1)
    0 (Function.uncurry angular) * Mc₀ ^ 2 * (‖Lq‖ * Mc₀)
  have hCmask : 0 ≤ Cmask :=
    mul_nonneg (mul_nonneg (cNorm_nonneg ..) (sq_nonneg _))
      (mul_nonneg (norm_nonneg _) hMc₀)
  have hamp := norm_carrierAmplitude_le_of_primitive_norms T current.Q F
    row col current.forward current.inverse initial ha' hcell angular D.field
    (carrierSupport_compact zRoot) hangular hang hsupportD (hν.mono hD) (hq.mono hD)
    hMc₀ (mul_nonneg (norm_nonneg _) hMc₀) hc.normal.low hqM
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)))
  obtain ⟨charts, symbols, hsymbols⟩ := exists_refined_kernel_inputs T current.Q
    F row col current.forward current.inverse initial
    hηb hr hr' ha' hrr haa har' hcell hP haR houterRadius hcarrier hf hInv htransverse
    hW₀ hL₀W₀ hcJ (hν.mono houter) (fun i ↦ (hdetreg i).mono houter)
  have hreg := refined_coefficients_regularity T current.Q F row col
    current.forward current.inverse initial hηb hr' ha' hcell (hν.mono houter)
    (fun i ↦ (hdetreg i).mono houter) hr hf hInv htransverse hcJ
  have hΩi := symbolDomain_open T current.Q hηb hr hInv htransverse hW₀ hL₀W₀
  have hpuncturedOpen : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_snd.snd
  obtain ⟨Cfreq, hCfreq, hdiffbound⟩ := exists_reference_differential_upper G
  have hn : 0 < n := by have := row.isLt; omega
  have hop := hconstruct d (transportPosition T current.Q) u J Ωi
    (symbolInputDomain zRoot ηb r (6 * a)) (conicMaskSupport zRoot ηb r' a')
    {p | ‖p.2.2‖ = 1 / 4} {p | p.2.2 ≠ 0} 1
    hZ le_rfl hΩi (ball_subset_closedBall.trans houtput)
    (symbolInverse_smooth T current.Q hηb hr hInv htransverse hL₀W₀)
    (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
    hgapA (fun _ hp ↦ transportAveragedGradient_symbolInverse T current.Q hηb hr hInv htransverse hp)
    ((symbolJacobian_eq_actual T current.Q hηb hr hf).mono (hWBi.trans hBiDom))
    (fun p hp ↦ hreg.jacobian_ne_zero p (hBiDom (hWBi hp)))
    (fun p hp ↦ hJacLow p (hWBi (hKiW hp))) le_rfl
    (by simpa only [mul_one, PrimitiveNormChart.carrier] using (le_rfl :
      1 + cNorm D.field.carrier (μ + 2) (transportPosition T current.Q) ≤
        1 + cNorm D.field.carrier (μ + 2) (transportPosition T current.Q)))
    hreg (symbolInverse_maps T current.Q hηb hr hInv htransverse)
    (fun p hp hx hy ha ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy ha)
    hpuncturedOpen (fun p hp ↦ norm_ne_zero_iff.mp (by rw [hp]; norm_num))
    (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
    (fun x hx v _ hv ↦ hshell x hx v hv) hcRaw
    (fun _ ht p ↦ symbolDomain_smul_iff T current.Q ht p)
    (fun _ ht _ hp ↦ symbolInverse_smul T current.Q hηb hr hInv htransverse hp ht)
    (fun _ ht _ hp ↦ symbolJacobian_scale_inverse T current.Q hηb hr hf hInv htransverse hp ht)
    hupper hpunctured (scaleFrequency_mem_fixed_sphere (by norm_num : (0 : ℝ) < 1 / 4))
    hn (4 * a') hsupport (by dsimp [μ]; omega) e (carrierSupport zRoot (r := a'))
    (carrierSupport_compact zRoot) hangular Cmask hCmask hkernel hamp
    (closedBall 0 (4 * a')) (FixedCutoffs.closedBall_four_subset_cell hcell) rfl
    (fun _ _ ↦ rfl) (FixedCutoffs.physical ha' 2)
    (fun _ hx ↦ FixedCutoffs.physical_eq_zero_outside_four ha' 2 hx)
    (FixedCutoffs.physical ha' 2).contDiff (FixedCutoffs.physical ha' 2).hasCompactSupport
    (fun _ hx ↦ FixedCutoffs.source_one_on_measurement ha' hx)
    charts symbols (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.1)
    (fun R hR x hx y hy ↦ (hsymbols R hR x hx y hy).2.2.2.2.1)
    (‖(adaptedSliceCoordinates T).equiv.symm.toContinuousLinearMap‖ * Cfreq)
    (mul_nonneg (norm_nonneg _) hCfreq.le)
    (fun _ hp ↦ symbolInverse_frequency_comparison T current.Q hηb hr hf hInv htransverse
      hsliceGap (fun D hD ↦ (hdiffbound D hD).1) hp)
  obtain ⟨_, _, _, _, _, _, _, hb, hA, Vop, hV, hVadj, htest, hsupp, huniq,
    hadj, _, hnormal⟩ := hop
  have hd : {d with high := FixedCutoffs.highFrequency} = d := rfl
  simp only [hd, mul_one] at hb hA hV hVadj hnormal
  let M := Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * Cnorm)) + 1
  refine ⟨M, by dsimp only [M]; positivity, Cpdo, hCpdo, hsupport, hb, hA, Vop,
    hV.trans ?_, hVadj.trans ?_, htest, hsupp, huniq, hadj, hnormal⟩ <;>
    dsimp only [M] <;> linarith

end JanetCartan.ContinuumNormal.ActualConstruction
