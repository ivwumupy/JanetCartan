module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.SeedAdmission

/-!
# Bounded carriers for the same finite normalized family

The retained geometric admission threshold is discharged by the actual
projected-stress scaling theorem on each supplied cell. One finite minimum
then fixes the scale interval and all carrier constants before the current
charts and original densities. The literal tests, adjoints, reflected normal
and common measurement restriction refer to the same selected operators.
The current chart family and the initialized finite incidence geometry remain
separate construction obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open PositiveReference.FlowConstruction RetainedRowGeometry ContinuumNormal.RetainedFrozen
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormal ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualComparison Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Construct bounded operators for every cell of one supplied retained family,
with the scale cap and all low/high constants chosen before the varying source
scale, current charts and original densities. The geometric premise is exactly
the C⁶-admission branch of `exists_retained_joint_comparison_geometry`; its
admission is proved from the same flat reference. No uniform operator bound,
normal estimate or source-matching identity is an input. Every local operator
retains its literal adjoint, uniqueness on tests and full reflected normal;
restriction to a common measurement radius retains that same operator and both
physical cutoff factors. The density class remains `μ+14`, with one high norm
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-realification`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_finite_retained_source_density_carriers
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    (P : ι → Patch n) {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ H.domain.chart n) (hbounded : Bornology.IsBounded U)
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    (Ω : ι → Set (Euclidean n × Euclidean 3)) (hΩ : ∀ i, IsOpen (Ω i))
    (zCell : ι → Euclidean 3) (ρc Rc B τlead L Mc : ι → ℝ) (row col : ι → Fin n)
    (hKΩ : ∀ i, closedBall ((0 : Euclidean n), zCell i) (ρc i) ⊆ Ω i)
    (hΩpatch : ∀ i, Ω i ⊆ (U ∩ ball 0 (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hRc : ∀ i, 0 < Rc i) (hτlead : ∀ i, 0 < τlead i)
    (hτRc : ∀ i, τlead i ≤ Rc i / 16) (hL : ∀ i, 0 < L i)
    (hbuffer : ∀ i, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i))
      (closedBall ((0 : Euclidean n), zCell i) (ρc i)))
    (hphysical : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (c₀ : (i : ι) → Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
      ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i) H.map)
    (htrans : ∀ i q, q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius →
      ⟪(normalizedHomogeneousSymbol hU (c₀ i).Q.1 (c₀ i).Q.2.1).hp q,
        (T i).data.adapted.normal⟫_ℝ ≠ 0)
    (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i, cNorm (Icc (-τlead i) (τlead i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRT : ∀ i, R i ≤ (T i).physicalRadius)
    (hRU : ∀ i, ball (0 : Euclidean n) (R i) ⊆ U)
    (hRtime : ∀ i, R i ≤ L i / (64 * Mc i))
    (V : ι → Set CarrierParameter) (hV : ∀ i, IsOpen (V i))
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (R i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell i) (Rc i) (τlead i)))
    (hlabel : ∀ i p, p ∈ ball (0 : Euclidean n) (R i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 64))
    (D : ι → CoefficientNormCharts n)
    (hD : ∀ i, (D i).field.region ⊆ ball (0 : Euclidean n) (R i) ×ˢ V i)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (hηb : ∀ i, ηb i ≠ 0)
    (r a r' a' : ι → ℝ) (hr : ∀ i, 0 < r i) (hr' : ∀ i, 0 < r' i)
    (ha' : ∀ i, 0 < a' i) (hcell : ∀ i, 4 * a' i < 1 / 2)
    (hrr : ∀ i, r' i ≤ r i) (haa : ∀ i, a' i ≤ a i)
    (har' : ∀ i, a' i ≤ r' i) (haR : ∀ i, 6 * a i < (T i).family.radius)
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (ha' i) 1) ×ˢ
      carrierSupport (z₀ i) (r := a' i) ⊆ (D i).field.carrier)
    (houter : ∀ i, coefficientDomain (z₀ i) (r i) (6 * a i) ⊆
      ball (0 : Euclidean n) (R i) ×ˢ V i)
    (p₀ : ι → InputVariables n) (q₀ : ι → Variables n × Euclidean 2)
    (ρ τ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hτ : ∀ i, 0 < τ i)
    (W Bi : ι → Set (InputVariables n)) (hW : ∀ i, IsOpen (W i))
    (hKiW : ∀ i, closedBall (p₀ i) (ρ i) ⊆ W i)
    (hBi : ∀ i, IsCompact (Bi i)) (hWBi : ∀ i, W i ⊆ Bi i)
    (hBiDom : ∀ i, Bi i ⊆ symbolInputDomain (z₀ i) (ηb i) (r i) (6 * a i))
    (hfoot : ∀ i p, p ∈ closedBall (p₀ i) (ρ i) → (D i).Contains p)
    (It : ι → Set ℝ) (hIt : ∀ i, IsOpen (It i)) (hIIt : ∀ i, Icc (0 : ℝ) 1 ⊆ It i)
    (hsegT : ∀ i t, t ∈ It i → MapsTo (transportSegmentInput n t) (W i) (D i).field.region)
    (hseg : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      MapsTo (transportSegmentInput n t) (W i) (D i).field.carrier)
    (A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (ε gap : ι → ℝ) (hε : ∀ i, 0 < ε i) (hgap : ∀ i, 0 < gap i)
    (hfreq : ∀ i p, p ∈ Bi i → ε i ≤ ‖p.2.2‖)
    (δgeometry : ι → ℝ) (hδgeometry : ∀ i, 0 < δgeometry i)
    (hgeometry : ∀ i, ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < (δgeometry i) →
      let Q := ⟨ProjectedStressFrame.projectedStress F,
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedSpectralGeometry (T i) Q (z₀ i) (ηb i) (r i) (a i) ∧
      closedBall (q₀ i) (2 * (τ i)) ⊆ symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)) ∧
      MapsTo (inverseCoordinates (symbolInverse (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i))))
        (closedBall (q₀ i) (2 * (τ i))) (closedBall (p₀ i) (ρ i)) ∧
      (∀ p ∈ closedBall (p₀ i) (ρ i), ‖(A i).symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition (T i) Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ (Bi i), (gap i) ≤ transportAbsoluteJacobian (adaptedSliceCoordinates (T i))
        (transportPosition (T i) Q) p) ∧
      (closure (augmentedTransportGradient (transportPosition (T i) Q) ''
        conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i))) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition (T i) Q) ''
          conicMaskSupport (z₀ i) (ηb i) (r' i) (a' i)) → (x, v) ∈ closedBall (q₀ i) (τ i)) ∧
      (∀ p ∈ symbolDomain (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)),
        ‖(symbolInverse (T i) Q (z₀ i) (ηb i) (r i) (6 * (a i)) p).2‖ ≤ 2 * ‖p.1.2.2‖)) :
    ∃ s > (0 : ℝ), s ≤ 1 / 8 ∧
    ∃ Cnorm Cpdo : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Cpdo i) ∧
    ∃ Bhigh : ι → ℕ → ℝ, (∀ i p, 0 < Bhigh i p) ∧
      ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ current : (i : ι) → Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ),
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4))) →
      (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zCell i) (L i / 4) → 0 < 1 + v i q) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCell i) (L i / 8))
        (2 * (n + 1) + 14) (v i) ≤ 1) →
      let e := fun i ↦ data (T i) (current i).Q (sourceDilation H.map σ) (row i) (col i)
        (current i).forward (current i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
        (ha' i) (hcell i)
        (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
        FixedCutoffs.highFrequency
      let d := fun i ↦ coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1)
      let J := fun i ↦ symbolJacobian (T i) (current i).Q
      let u := fun i ↦ symbolInverse (T i) (current i).Q (z₀ i) (ηb i) (r i) (6 * a i)
      let Ωi := fun i ↦ symbolDomain (T i) (current i).Q (z₀ i) (ηb i) (r i) (6 * a i)
      let S := fun i ↦ closedBall (spectatorCenter (z₀ i)) (a' i / 2)
      ∃ hsupport : ∀ i x, (d i).measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' i,
      ∃ hbsmooth : ∀ i, ContDiff ℝ ∞
        (Function.uncurry (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i))),
      ∃ hA : ∀ i l j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i) ξ z l j)
        (2 * (n + 1) + 1) (Cpdo i),
      ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n, ∀ i,
        ‖(Vop i)‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
        ‖(Vop i).adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
        (∀ f : carrierInitialTestSpace n,
          (Vop i) (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (e i).outputChart → (Vop i) f x = 0) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ f : carrierInitialTestSpace n,
            Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) → Wop = (Vop i)) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
          (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        (realQuadratureChannel (Vop i)).comp (realQuadratureChannel (Vop i)).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator (by have := (row i).isLt; omega) (4 * (a' i))
              (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i)) (hbsmooth i)
              (fullReflectedMatrixAmplitude_supportedInCenteredBox (d i) (J i) (u i) (Ωi i) (S i) (4 * (a' i)) (hsupport i))
              (Cpdo i) (fun l j ξ is his ↦ (hA i) l j ξ is (by omega)))) ∧
        (∀ p l j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i) ξ z l j) p
          ((Bhigh i) p * (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), (zCell i)) ((L i) / 8)) p (v i)))) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < (a' i) →
          let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
          let Vb := CommonMeasurement.restrictCarrier χ (Vop i)
          let eb := data (T i) (current i).Q (sourceDilation H.map σ) (row i) (col i) (current i).forward (current i).inverse
            (fun q ↦ positiveDensityAmplitude σ ((v i) q)) hb hbcell
            (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
            FixedCutoffs.highFrequency
          let db := coefficientsOfCarrier eb (FixedCutoffs.physical hb 1)
          let Aop := vectorTwoPositionL2Operator (by have := (row i).isLt; omega) (4 * (a' i))
            (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i)) (hbsmooth i)
            (fullReflectedMatrixAmplitude_supportedInCenteredBox (d i) (J i) (u i) (Ωi i) (S i) (4 * (a' i)) (hsupport i))
            (Cpdo i) (fun l j ξ is his ↦ (hA i) l j ξ is (by omega))
          let multiplier := freezingVectorPhysicalMultiplier (FixedCutoffs.physical hb 1)
            (FixedCutoffs.physical hb 1).continuous (FixedCutoffs.physical hb 1).hasCompactSupport
          ‖Vb‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * (a' i)) * (Cnorm i))) ∧
          (∀ f : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral eb f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
          carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
            realOutputCompression (transferOperator (multiplier ∘L Aop ∘L multiplier)) ∧
          db = CommonMeasurement.restrictCoefficients (d i) (FixedCutoffs.physical hb 1) ∧
          fullReflectedMatrixAmplitude db (J i) (u i) (Ωi i) (S i) =
            CommonMeasurement.restrictAmplitude (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i))
              (FixedCutoffs.physical hb 1) := by
  classical
  have hi : IsImmersionOn H.map U := isImmersionOn_of_isIsometricOn
    (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one) (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUG hx)
  have hlocal (i : ι) := exists_retained_chart_source_density_carrier
    (hP i) (T i) (hΩ i) (hKΩ i) (hΩpatch i) (hRc i) (hτlead i) (hτRc i)
    (hbuffer i) H.contDiff hi hrank (hphysical i) (c₀ i) (htrans i)
    (fun x _ ↦ H.inducedMetric_eq_one x) (hL i) (hMc i) (hforward i)
    (hR i) (hRT i) (hRU i) (hRtime i) (hV i) (hVP i) (hflow i)
    (D i) (hD i) (hlabel i) (z₀ i) (hηb i) (hr i) (hr' i) (ha' i)
    (hrr i) (haa i) (har' i) (hcell i) (haR i) (houter i) (hsupportD i)
    (p₀ i) (q₀ i) (hρ i) (hτ i) (hW i) (hKiW i) (hBi i) (hWBi i)
    (hBiDom i) (hfoot i) (hIt i) (hIIt i) (hsegT i) (hseg i) (A i)
    (hε i) (hgap i) (hfreq i)
  choose s hs _ Cnorm hCnorm Cpdo hCpdo Bhigh hBhigh hconstruct using hlocal
  choose sframe hsframe _ hadmission using fun i ↦
    SourceMatching.exists_joint_stress_scale_interval H hbounded (hδgeometry i)
  obtain ⟨s₀, hs₀, hs₀le⟩ := (finite_range (fun i ↦ min (s i) (sframe i))).isCompact.exists_forall_le'
    continuousOn_id (by rintro t ⟨i, rfl⟩; exact lt_min (hs i) (hsframe i))
  refine ⟨min s₀ (1 / 8), lt_min hs₀ (by norm_num), min_le_right _ _,
    Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, ?_⟩
  intro σ hσ current v hv hpos hinterval hvnorm e d J u Ωi S
  have hsmallcap (i : ι) : σ ≤ min (s i) (sframe i) :=
    hσ.2.trans ((min_le_left _ _).trans (hs₀le _ ⟨i, rfl⟩))
  have hconstruct' (i : ι) := hconstruct i σ
    ⟨hσ.1, (hsmallcap i).trans (min_le_left _ _)⟩ (current i)
  have hgeometry' (i : ι) := by
    obtain ⟨hiσ, hrankσ, hframeσ, hsmallσ⟩ :=
      hadmission i σ hσ.1 ((hsmallcap i).trans (min_le_right _ _))
    have hFσ : ContDiffOn ℝ ∞ (sourceDilation H.map σ) U :=
      (contDiff_sourceDilation H.contDiff).contDiffOn
    have hsmall : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
        δgeometry i := by
      apply (cNorm_mono_set_of_contDiffAt ((hphysical i).trans subset_closure)
        hbounded.isCompact_closure ?_).trans_lt hsmallσ
      intro x hx
      exact ((hframeσ x hx).sub contDiffAt_const).of_le (by simp)
    have hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (ProjectedStressFrame.projectedStress (sourceDilation H.map σ) - fun _ ↦ cubeStress n) <
        (T i).family.threshold := by
      rw [← (current i).frame_eq]
      exact (current i).Q.2.2
    have hgeom := hgeometry i (sourceDilation H.map σ) hFσ hiσ hrankσ hlow hsmall
    have hQ : (⟨ProjectedStressFrame.projectedStress (sourceDilation H.map σ),
        contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hFσ hiσ hrankσ),
        hlow⟩ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T i).family.threshold}) = (current i).Q :=
      Subtype.ext (current i).frame_eq.symm
    dsimp only at hgeom
    rw [hQ] at hgeom
    exact hgeom
  have hcarrier (i : ι) := hconstruct' i (hgeometry' i).1 (hgeometry' i).2.1
    (hgeometry' i).2.2.1 (hgeometry' i).2.2.2.1 (hgeometry' i).2.2.2.2.1
    (hgeometry' i).2.2.2.2.2.1 (hgeometry' i).2.2.2.2.2.2.1
    (hgeometry' i).2.2.2.2.2.2.2 (v i) (hv i) (hpos i) (hinterval i) (hvnorm i)
  choose hsupport hbsmooth hA Vop hop using hcarrier
  exact ⟨hsupport, hbsmooth, hA, Vop, hop⟩

end JanetCartan.ContinuumRow.NormalizedSelection
