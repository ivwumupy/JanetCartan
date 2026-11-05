module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedDensityProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.TransportProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement

/-!
# Bounded normalized carriers on the original retained conic geometry

Apply the supported-shell construction to the original retained source charts
and their positive-density class. The coefficient and Hamilton-position
budgets are derived from the seed before source scale. The output is the
literal uncut carrier, its adjoint and its full reflected matrix normal;
no operator, amplitude or normal-gap estimate is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open PositiveReference.FlowConstruction RetainedRowGeometry ContinuumNormal.RetainedFrozen
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormal ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualComparison Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Construct the bounded carrier and literal adjoint with constants before
source scale and every density in the original `μ+14` class. The supplied
conic geometry is the current branch of
`RetainedJointGeometry.exists_retained_joint_comparison_geometry`, on the SAME
radii and masks. All coefficient budgets and supported normal estimates are
conclusions. All high amplitude orders retain one high norm of the original density.
The common measurement restriction keeps the literal integrals and the full
physical normal, including both measurement factors. Uniqueness on literal
tests is retained for the subsequent finite row assembly
(`app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-realification`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_retained_chart_source_density_carrier
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc Bflow τ L Mc : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hΩpatch : Ω ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τ) τ ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U) (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (zRoot : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (haR : 6 * a < T.family.radius)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
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
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖) :
    ∃ s > (0 : ℝ), s ≤ 1 / 8 ∧
    ∃ Cnorm > (0 : ℝ), ∃ Cpdo > (0 : ℝ),
    ∃ B : ℕ → ℝ, (∀ p, 0 < B p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc Bflow τ row col (sourceDilation F σ),
      RetainedSpectralGeometry T current.Q zRoot ηb r a →
      closedBall q₀ (2 * τi) ⊆ symbolDomain T current.Q zRoot ηb r (6 * a) →
      MapsTo (inverseCoordinates (symbolInverse T current.Q zRoot ηb r (6 * a)))
        (closedBall q₀ (2 * τi)) (closedBall p₀ ρi) →
      (∀ p ∈ closedBall p₀ ρi, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T current.Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T current.Q) p) →
      (closure (augmentedTransportGradient (transportPosition T current.Q) ''
        conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain T current.Q zRoot ηb r (6 * a)) →
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T current.Q) ''
          conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τi) →
      (∀ p ∈ symbolDomain T current.Q zRoot ηb r (6 * a),
        ‖(symbolInverse T current.Q zRoot ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
      let e := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
        (fun q ↦ positiveDensityAmplitude σ (v q)) ha' hcell
        (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
      let J := symbolJacobian T current.Q
      let u := symbolInverse T current.Q zRoot ηb r (6 * a)
      let Ωi := symbolDomain T current.Q zRoot ηb r (6 * a)
      let S := closedBall (spectatorCenter zRoot) (a' / 2)
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ωi S)),
      ∃ hA : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j) (2 * (n + 1) + 1) Cpdo,
      ∃ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖Vop‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * Cnorm)) ∧
        ‖Vop.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * Cnorm)) ∧
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
              Cpdo (fun i j ξ is his ↦ hA i j ξ is (by omega)))) ∧
        (∀ p i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j) p
          (B p * (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) p v))) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' →
          let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
          let Vb := CommonMeasurement.restrictCarrier χ Vop
          let eb := data T current.Q (sourceDilation F σ) row col current.forward current.inverse
            (fun q ↦ positiveDensityAmplitude σ (v q)) hb hbcell
            (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
            FixedCutoffs.highFrequency
          let db := coefficientsOfCarrier eb (FixedCutoffs.physical hb 1)
          let Aop := vectorTwoPositionL2Operator (by have := row.isLt; omega) (4 * a')
            (fullReflectedMatrixAmplitude d J u Ωi S) ‹ContDiff ℝ ∞ _›
            (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ωi S (4 * a') hsupport)
            Cpdo (fun i j ξ is his ↦ hA i j ξ is (by omega))
          let multiplier := freezingVectorPhysicalMultiplier (FixedCutoffs.physical hb 1)
            (FixedCutoffs.physical hb 1).continuous (FixedCutoffs.physical hb 1).hasCompactSupport
          ‖Vb‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') * Cnorm)) ∧
          (∀ f : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral eb f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
          carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
            realOutputCompression (transferOperator (multiplier ∘L Aop ∘L multiplier)) ∧
          db = CommonMeasurement.restrictCoefficients d (FixedCutoffs.physical hb 1) ∧
          fullReflectedMatrixAmplitude db J u Ωi S =
            CommonMeasurement.restrictAmplitude (fullReflectedMatrixAmplitude d J u Ωi S)
              (FixedCutoffs.physical hb 1) := by
  let E := ball (0 : Euclidean n) R ×ˢ V
  let D' : CoefficientNormCharts n := {D with field := {
    D.field with region := E
                 isOpen_region := isOpen_ball.prod hV
                 ball_subset := D.field.ball_subset.trans hD }}
  let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  let μ := 2 * (n + 1) + 1
  obtain ⟨Mc₀, hMc₀, Bc₀, hBc₀, hcoeff⟩ := exists_retained_chart_source_density_profiles
    hP T hΩ hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hL hMc hforward hR hRT hRU hRtime hV hVP hflow D' Subset.rfl hlabel ha' hcell
    angular FixedCutoffs.highFrequency (angularMask_smooth ..).contDiffOn
    FixedCutoffs.highFrequency_smooth.contDiffOn
  have hphase : D.field.region ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    fun p hp ↦ ⟨ball_subset_ball hRT (hD hp).1, hVP (hD hp).2⟩
  obtain ⟨sp, hsp, _, Hp, hHp, hposition⟩ :=
    exists_actual_source_transportPosition_profiles T seed.Q hP hF hrank hphysical
      seed.frame_eq htrans D.field hphase
  obtain ⟨Cnorm, hCnorm, Cpdo, hCpdo, hconstruct⟩ :=
    exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρi hτi hW hKiW hBi hWBi
      (O := ball q₀ (2 * τi)) isOpen_ball (closedBall_subset_ball (by linarith))
      D.field.isOpen_region (isCompact_closedBall _ _) D.field.ball_subset
      hIt hIIt hsegT hseg A (hHp 3).le hMc₀.le
      (show 1 ≤ 2 * Bc₀ μ by linarith [hBc₀ μ]) hgap hε (show 0 ≤ 1 + Hp (μ + 2) by linarith [hHp (μ + 2)])
      (fun p hp ↦ hfreq p (hWBi (hKiW hp))) D' hfoot
      (Cupper := 2) (ℓ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (S := closedBall (spectatorCenter zRoot) (a' / 2)) (isCompact_closedBall _ _)
      μ (by dsimp [μ]; omega) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
      FixedCutoffs.radialRegularization_smooth FixedCutoffs.radialRegularization_compact
      (fun _ ht ↦ FixedCutoffs.radialRegularization_one ht)
  choose Ch hCh hhighConstruct using fun p ↦
    exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms (N := N)
      (adaptedSliceCoordinates T) p₀ q₀ hρi hτi hW hKiW hBi hWBi
      (O := ball q₀ (2 * τi)) isOpen_ball (closedBall_subset_ball (by linarith))
      D.field.isOpen_region (isCompact_closedBall _ _) D.field.ball_subset
      hIt hIIt hsegT hseg A (hHp 3).le hMc₀.le (hBc₀ (max p 2)) hgap hε
      (show 0 ≤ 1 + Hp (max p 2 + 2) by linarith [hHp (max p 2 + 2)])
      (fun q hq ↦ hfreq q (hWBi (hKiW hq))) D' hfoot
      (Cupper := 2) (ℓ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (S := closedBall (spectatorCenter zRoot) (a' / 2)) (isCompact_closedBall _ _)
      (max p 2) (le_max_right _ _) FixedCutoffs.highFrequency_smooth
      (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
  refine ⟨min sp (1 / 8), lt_min hsp (by norm_num), min_le_right _ _,
    Cnorm, hCnorm, Cpdo, hCpdo, fun p ↦ Ch p + Cpdo,
    fun p ↦ add_pos (hCh p) hCpdo, ?_⟩
  intro σ hσ current hspectral houtput hrange hgapA hJacLow hpunctured hshell hupper
    v hv hpos hinterval hvnorm e d J u Ωi S
  obtain ⟨hcoeffHigh, hc⟩ := hcoeff σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
    current v hv hpos hinterval hvnorm
  have hcRaw := hc
  rw [coefficientsOfCarrier_data] at hc
  obtain ⟨hZ, hZbound⟩ :=
    hposition σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ current.Q current.frame_eq
  obtain ⟨houterRadius, hcarrier, G, β, cJ, W₀, L₀, hcJ, hW₀, hL₀W₀,
    hf, hInv, htransverse, hsliceGap⟩ := hspectral
  let initial := fun q ↦ positiveDensityAmplitude σ (v q)
  have hν : ContDiffOn ℝ ∞
      (Function.uncurry (normalField T current.Q (sourceDilation F σ) row col
        current.forward current.inverse initial)) E := hc.normal.smooth
  have hdetreg (i : Fin n) : ContDiffOn ℝ ∞
      (fun p : Euclidean n × CarrierParameter ↦
        quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2)) i) E :=
    contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn
      ((quadratic_canonical_smooth T hP current.Q).mono
        (fun p hp ↦ ⟨⟨hRU hp.1, ball_subset_ball hRT hp.1⟩,
          fun i ↦ (hVP hp.2 i).trans (by linarith only [hP.1])⟩))) i
  have hq : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      quadratic (current.Q.1 p.1) (T.carrierGradient current.Q p.1 (parameter p.2))) E :=
    (contDiffOn_piLp 2).mpr hdetreg
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
    (sourceDilation F σ) row col current.forward current.inverse initial ha' hcell angular
    D.field.isOpen_region hZ.continuousOn (hν.mono hD).continuousOn (hq.mono hD).continuousOn
    hang.continuous hangular (hsupportD.trans D.field.ball_subset)
  let Cmask := cNorm (carrierSupport zRoot (r := a') ×ˢ closedBall (0 : Euclidean (n - 1)) 1)
    0 (Function.uncurry angular) * Mc₀ ^ 2 * (‖Lq‖ * Mc₀)
  have hCmask : 0 ≤ Cmask :=
    mul_nonneg (mul_nonneg (cNorm_nonneg ..) (sq_nonneg _))
      (mul_nonneg (norm_nonneg _) hMc₀.le)
  have hamp := norm_carrierAmplitude_le_of_primitive_norms T current.Q (sourceDilation F σ)
    row col current.forward current.inverse initial ha' hcell angular D.field
    (carrierSupport_compact zRoot) hangular hang hsupportD (hν.mono hD) (hq.mono hD)
    hMc₀.le (mul_nonneg (norm_nonneg _) hMc₀.le) hc.normal.low hqM
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)))
  obtain ⟨charts, symbols, hsymbols⟩ := exists_refined_kernel_inputs T current.Q
    (sourceDilation F σ) row col current.forward current.inverse initial
    hηb hr hr' ha' hrr haa har' hcell hP haR houterRadius hcarrier hf hInv htransverse
    hW₀ hL₀W₀ hcJ (hν.mono houter) (fun i ↦ (hdetreg i).mono houter)
  have hreg := refined_coefficients_regularity T current.Q (sourceDilation F σ) row col
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
    hZ (hZbound 3) hΩi (ball_subset_closedBall.trans houtput)
    (symbolInverse_smooth T current.Q hηb hr hInv htransverse hL₀W₀)
    (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
    hgapA (fun _ hp ↦ transportAveragedGradient_symbolInverse T current.Q hηb hr hInv htransverse hp)
    ((symbolJacobian_eq_actual T current.Q hηb hr hf).mono (hWBi.trans hBiDom))
    (fun p hp ↦ hreg.jacobian_ne_zero p (hBiDom (hWBi hp)))
    (fun p hp ↦ hJacLow p (hWBi (hKiW hp))) le_rfl
    (by simpa only [mul_one, PrimitiveNormChart.carrier] using add_le_add (le_refl (1 : ℝ)) (hZbound (μ + 2)))
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
  refine ⟨hsupport, hb, hA, Vop, hV, hVadj, htest, hsupp, huniq, hadj, hnormal, ?_, ?_⟩
  · intro p i j
    let Hv := 1 + cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) p v
    have hHv : 1 ≤ Hv := by
      have hn := cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) p v
      dsimp [Hv]
      linarith
    by_cases hp : 2 ≤ p
    · have hcHigh : D'.Controls (max p 2) Mc₀ (Bc₀ (max p 2)) Hv d := by
        simpa only [max_eq_left hp] using hcoeffHigh p
      have hZHigh : 1 + cNorm D.field.carrier (max p 2 + 2)
          (transportPosition T current.Q) ≤ (1 + Hp (max p 2 + 2)) * Hv :=
        (add_le_add (le_refl (1 : ℝ)) (hZbound _)).trans
          (le_mul_of_one_le_right (by linarith [hHp (max p 2 + 2)]) hHv)
      obtain ⟨_, hentry, _⟩ := hhighConstruct p d (transportPosition T current.Q) u J Ωi
        (symbolInputDomain zRoot ηb r (6 * a)) (conicMaskSupport zRoot ηb r' a')
        {p | ‖p.2.2‖ = 1 / 4} {p | p.2.2 ≠ 0} Hv
        hZ (hZbound 3) hΩi (ball_subset_closedBall.trans houtput)
        (symbolInverse_smooth T current.Q hηb hr hInv htransverse hL₀W₀)
        (hrange.mono (closedBall_subset_closedBall (by linarith)) Subset.rfl)
        hgapA (fun _ hq ↦ transportAveragedGradient_symbolInverse T current.Q hηb hr hInv htransverse hq)
        ((symbolJacobian_eq_actual T current.Q hηb hr hf).mono (hWBi.trans hBiDom))
        (fun q hq ↦ hreg.jacobian_ne_zero q (hBiDom (hWBi hq)))
        (fun q hq ↦ hJacLow q (hWBi (hKiW hq))) hHv hZHigh
        hreg (symbolInverse_maps T current.Q hηb hr hInv htransverse)
        (fun q hq hx hy ha ↦ primitive_masks_mem_conicMaskSupport hηb hr' ha' hq.2.2.1 hx hy ha)
        hpuncturedOpen (fun q hq ↦ norm_ne_zero_iff.mp (by rw [hq]; norm_num))
        (fun q hq ↦ hpunctured ⟨hq.1, hq.2.1⟩)
        (fun x hx v _ hv ↦ hshell x hx v hv) hcHigh
        (fun _ ht q ↦ symbolDomain_smul_iff T current.Q ht q)
        (fun _ ht _ hq ↦ symbolInverse_smul T current.Q hηb hr hInv htransverse hq ht)
        (fun _ ht _ hq ↦ symbolJacobian_scale_inverse T current.Q hηb hr hf hInv htransverse hq ht)
        hupper hpunctured (scaleFrequency_mem_fixed_sphere (by norm_num : (0 : ℝ) < 1 / 4))
      rw [hd] at hentry
      intro ξ is his z
      exact (hentry i j ξ is (his.trans (le_max_left _ _)) z).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpdo.le) (zero_le_one.trans hHv))
    · intro ξ is his z
      exact (hA i j ξ is (his.trans (by dsimp [μ]; omega)) z).trans
        ((le_add_of_nonneg_left (hCh p).le).trans
          (le_mul_of_one_le_right (add_pos (hCh p) hCpdo).le hHv))
  · intro b hbmeasure hbcell hba χ Vb eb db Aop multiplier
    obtain ⟨hVb, htestb, hadjb, hsuppb, hnormalb⟩ :=
      CommonMeasurement.fixed_common_restriction e hbmeasure ha' hbcell hcell hba
        rfl (fun _ _ ↦ rfl) rfl Vop htest hadj _ hnormal
    have hdb : db = CommonMeasurement.restrictCoefficients d (FixedCutoffs.physical hbmeasure 1) := by
      dsimp only [db, d, eb, e]
      unfold coefficientsOfCarrier CommonMeasurement.restrictCoefficients
      congr 1
      funext x
      exact (CommonMeasurement.physical_measurement_mul hbmeasure ha'
        (by linarith : 3 * b ≤ 2 * a') x).symm
    exact ⟨hVb.trans hV, htestb, hadjb, hsuppb, hnormalb, hdb,
      hdb ▸ CommonMeasurement.fullReflectedMatrixAmplitude_restrictCoefficients
        d (FixedCutoffs.physical hbmeasure 1) J u Ωi S⟩

end JanetCartan.ContinuumRow.NormalizedSelection
