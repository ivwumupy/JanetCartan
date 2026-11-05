module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FiniteDensityCarriers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SourceFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedDensityActions
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredData

/-!
# Actual source charts and bounded carriers on one retained finite family

Instantiate the normalized chart constructor and bounded-carrier construction
on the same supplied seeds and coefficient domains. A common cap and all
carrier constants precede the varying scale and original density. No current
chart existence, source identity or analytic carrier estimate is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open NormalizedBackground.SourceGeometry
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference
open PositiveReference.FlowConstruction RetainedRowGeometry ContinuumNormal.RetainedFrozen
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormal ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open FullPhaseCharts ActualComparison Pseudodifferential AmplitudeBound PeriodicLocalL2
open ContinuumNormal.FrozenModel ContinuumNormal.SourceDensityLimitRealization

/-- Construct the source charts and their bounded density carriers on the SAME
retained finite seeds. The original ODE lifts, forward/inverse identities,
scalar transport, literal test and adjoint actions, reflected normals and
common measurement restrictions are retained together. Weighted normalized
kernels and both actions are identified on the actual current ODE labels.
Every supplied normalized-adjoint realization equals this SAME bounded carrier,
including the unweighted case at zero density. All bounds precede
scale and densities in the original `μ+14` class. The coefficient-domain
contraction and primitive conic inputs are supplied by the original selection;
there is no free current-chart or analytic-bound premise. Consumers are the
normalized measured row and `PositiveBackground.SourceInverse`
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-realification`, `app:ch_background:prop:bg-adjoint`). -/
theorem exists_finite_seed_source_density_carriers_with_normalized_actions
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
    (hRc : ∀ i, 0 < Rc i) (hB : ∀ i, 0 ≤ B i)
    (hτeq : ∀ i, τlead i = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hL : ∀ i, 0 < L i)
    (hΩscale : ∀ i σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω i) (Ω i))
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
    ∃ Cnorm Cpdo : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Cpdo i) ∧
    ∃ Bhigh : ι → ℕ → ℝ, (∀ i p, 0 < Bhigh i p) ∧
    ∃ cap > (0 : ℝ), cap ≤ 1 / 8 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (i : ι) →
      Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ),
    (∀ σ hσ i,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        ODE.IsSmoothFlowOn (liftedDirection (T i) (current σ hσ i).Q (row i) (col i))
          (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i) (Rc i / 2)
          (existenceTime (Rc i) (liftedLowBound (T i) (B i))) Ψ ∧
        (current σ hσ i).forward = forwardFromLift Ψ ∧
        (current σ hσ i).inverse = footpointFromLift Ψ ∧
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δgeometry i ∧
        EqOn (current σ hσ i).forward (sourceTransportFlow (c₀ i).forward σ)
          (Ioo (-τlead i) (τlead i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) ∧
        EqOn (current σ hσ i).inverse (sourceTransportFlow (c₀ i).inverse σ)
          (current σ hσ i).D ∧
        EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
          (sourceAmplitude ((c₀ i).scalar (fun _ ↦ 1)) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
            carrierNullvector (T i) (current σ hσ i).Q (col i) w)
          (sourceAmplitude (fun w ↦ (c₀ i).scalar (fun _ ↦ 1) w •
            carrierNullvector (T i) (c₀ i).Q (col i) w) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
            (fun w ↦ sourceAmplitude ((c₀ i).scalar (fun _ ↦ 1)) σ w *
              weight ((current σ hσ i).inverse (coordinates (adaptedCoordinates (T i).data.adapted) w)))
            ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D)) ∧
      ∀ σ hσ, let current := current σ hσ
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
      ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n, (∀ i,
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
              (FixedCutoffs.physical hb 1)) ∧
      ∀ i,
        let unit := normalizedCarrierData (T i) (c₀ i).Q H.map (row i) (col i)
          (c₀ i).forward (c₀ i).inverse (fun _ ↦ 1) (ha' i) (hcell i)
          (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
            (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
        let normalized := weightNormal unit
          (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (T i) (current i).inverse p)))
        carrierKernel (e i) = carrierKernel normalized ∧
        carrierTestIntegral (e i) = carrierTestIntegral normalized ∧
        carrierAdjointIntegral (e i) = carrierAdjointIntegral normalized ∧
        (∀ f : carrierInitialTestSpace n,
          Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalized f.val) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral normalized w) 2 (carrierMeasure n) ∧
          (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w) ∧
        (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w) →
          Wop = Vop i) ∧
        (v i = (fun _ ↦ 0) → ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral unit w) →
          Wop = Vop i) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' i →
          let unitb := normalizedCarrierData (T i) (c₀ i).Q H.map (row i) (col i)
            (c₀ i).forward (c₀ i).inverse (fun _ ↦ 1) hb hbcell
            (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
          let normalizedb := weightNormal unitb
            (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (T i) (current i).inverse p)))
          let Vb := CommonMeasurement.restrictCarrier (FixedCutoffs.periodic hb hbcell 1) (Vop i)
          (∀ f : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalizedb f.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral normalizedb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w) ∧
          (∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w) →
            Wop = Vb) ∧
          (v i = (fun _ ↦ 0) → ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral unitb w) →
            Wop = Vb ∧ ∀ f : carrierInitialTestSpace n,
              Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral unitb f.val) := by
  classical
  have hτlead (i : ι) : 0 < τlead i := by
    rw [hτeq i]
    exact div_pos (existenceTime_pos (hRc i) (liftedLowBound_nonneg (T i) (hB i))) (by norm_num)
  have hτRc (i : ι) : τlead i ≤ Rc i / 16 := by
    have hh := (existenceTime_le (hRc i) (liftedLowBound_nonneg (T i) (hB i))).1
    rw [hτeq i]
    linarith
  obtain ⟨sb, hsb, hsb8, Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, hcarrier⟩ :=
    exists_finite_retained_source_density_carriers H P hUG hbounded T hP Ω hΩ
      zCell ρc Rc B τlead L Mc row col hKΩ hΩpatch hRc hτlead hτRc hL hbuffer
      hphysical c₀ htrans hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel
      D hD z₀ ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter
      p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
      A ε gap hε hgap hfreq δgeometry hδgeometry hgeometry
  have hpatch (i : ι) : Ω i ⊆ ball 0 (T i).physicalRadius ×ˢ parameterCube (2 * (P i).radius) :=
    fun w hw ↦ ⟨(hΩpatch i hw).1.2,
      fun j ↦ ((hΩpatch i hw).2 j).le.trans (by linarith only [(hP i).1])⟩
  obtain ⟨sc, hsc, _, current, hcurrent⟩ :=
    NormalizedChartFamily.exists_finite_source_charts_with_lifts H hUG hbounded T Ω hΩ
      zCell ρc Rc B τlead δgeometry row col hRc hB hδgeometry hτeq hKΩ hpatch
      (fun i _ hw ↦ (hΩpatch i hw).1.1) hΩscale hphysical hbuffer c₀ htrans
  refine ⟨Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh,
    min sb sc, lt_min hsb hsc, (min_le_left _ _).trans hsb8,
    fun σ hσ ↦ current σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩,
    (fun σ hσ i ↦ hcurrent σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩ i), ?_⟩
  intro σ hσ current' v hv hpos hinterval hvnorm e d J u Ωi S
  obtain ⟨hsupport, hbsmooth, hA, Vop, hVop⟩ :=
    hcarrier σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ current' v hv hpos hinterval hvnorm
  refine ⟨hsupport, hbsmooth, hA, Vop, hVop, ?_⟩
  intro i unit normalized
  have hpatchInterior : Ω i ⊆ ball 0 (T i).physicalRadius ×ˢ
      parameterInterior (2 * (P i).radius) := by
    intro w hw
    exact ⟨(hΩpatch i hw).1.2,
      fun j ↦ ((hΩpatch i hw).2 j).trans (by linarith only [(hP i).1])⟩
  have hsupp : ∀ (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1)),
      FixedCutoffs.periodic (ha' i) (hcell i) 1 x ≠ 0 →
      angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
        (angularWidth_spec (hηb i) (hr' i)).1 z η ≠ 0 →
      densityCoordinates (T i) (centeredTorusRepresentative x, z) ∈
        Ioo (-τlead i) (τlead i) ×ˢ
          ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 32) := by
    intro x z η hx hz
    apply (outputCylinder_spec (hRc i) (hτlead i)).2
    apply hflow i
    apply hD i
    apply (D i).field.ball_subset
    apply hsupportD i
    change FixedCutoffs.physical (ha' i) 1 (centeredTorusRepresentative x) ≠ 0 at hx
    have hmask : (z, η) ∈ tsupport (Function.uncurry
        (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
          (angularWidth_spec (hηb i) (hr' i)).1)) := subset_tsupport _ hz
    exact ⟨subset_tsupport _ hx,
      (angularMask_tsupport (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
        (angularWidth_spec (hηb i) (hr' i)).1 hmask).1⟩
  have hσ1 : σ ≤ 1 := (hσ.2.trans (min_le_left _ _)).trans (hsb8.trans (by norm_num))
  obtain ⟨hkernel, htestEq, hadjointEq⟩ := retained_chart_weighted_normalized_kernel_and_integrals
    (hP i) (T i) (hΩ i) (hKΩ i) hpatchInterior (hRc i) (hτlead i) (hτRc i)
    (hbuffer i) H.contDiff (fun x hx ↦ H.fullNormalRank x (hUG hx)) (hphysical i)
    (c₀ i) (htrans i) (fun x _ ↦ H.inducedMetric_eq_one x) (ha' i) (hcell i)
    (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (ha' i)
      (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency hsupp
    hσ.1 hσ1 (current' i) (fun q ↦ Real.sqrt (1 + v i q))
  obtain ⟨_, _, htest, _, _, hadjoint, _⟩ := hVop i
  have hrep : ∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral normalized w) 2 (carrierMeasure n) ∧
      (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w := by
    intro w
    rw [← hadjointEq]
    exact hadjoint w
  have huniq (Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
      (hWop : ∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalized w) :
      Wop = Vop i := by
    have he : Wop.adjoint = (Vop i).adjoint := by
      ext1 w
      exact Lp.ext ((hWop w).trans (hrep w).2.symm)
    simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
  have htestn : ∀ f : carrierInitialTestSpace n,
      Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalized f.val := by
    intro f
    rw [← htestEq]
    exact htest f
  refine ⟨hkernel, htestEq, hadjointEq, htestn, hrep, huniq, ?_, ?_⟩
  · intro hvzero Wop hWop
    apply huniq Wop
    have hn : normalized = unit := by
      simp only [normalized, hvzero, add_zero, Real.sqrt_one, weightNormal, one_smul]
    simpa only [hn] using hWop
  · intro b hb hbcell hba unitb normalizedb Vb
    have hmeas := NormalizedMeasurement.supplied_carrier_common_measurement normalized
      hb (ha' i) hbcell (hcell i) hba rfl (fun _ _ ↦ rfl) rfl
    obtain ⟨_, htestb, hadjb⟩ := hmeas.2.2.2.2.2.2.2.2 (Vop i)
    have htestbn : ∀ f : carrierInitialTestSpace n,
        Vb (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral normalizedb f.val :=
      (htestb htestn).1
    have hrepb : ∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral normalizedb w) 2 (carrierMeasure n) ∧
        Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w := hadjb hrep
    have huniqb (Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (hWop : ∀ w, Wop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral normalizedb w) :
        Wop = Vb := by
      have he : Wop.adjoint = Vb.adjoint := by
        ext1 w
        exact Lp.ext ((hWop w).trans (hrepb w).2.symm)
      simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint he
    refine ⟨htestbn, hrepb, huniqb, ?_⟩
    intro hvzero Wop hWop
    have hn : normalizedb = unitb := by
      simp only [normalizedb, hvzero, add_zero, Real.sqrt_one, weightNormal, one_smul]
    have he : Wop = Vb := huniqb Wop (by simpa only [hn] using hWop)
    exact ⟨he, fun f ↦ by simpa only [he, hn] using htestbn f⟩

/-- Preserve the original finite density-carrier API by projecting the SAME
operators constructed with normalized actions. No chart, mask, amplitude or
operator is selected again (`app:ch_background:defn:bg-row`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_finite_seed_source_density_carriers
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
    (hRc : ∀ i, 0 < Rc i) (hB : ∀ i, 0 ≤ B i)
    (hτeq : ∀ i, τlead i = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hL : ∀ i, 0 < L i)
    (hΩscale : ∀ i σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω i) (Ω i))
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
    ∃ Cnorm Cpdo : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Cpdo i) ∧
    ∃ Bhigh : ι → ℕ → ℝ, (∀ i p, 0 < Bhigh i p) ∧
    ∃ cap > (0 : ℝ), cap ≤ 1 / 8 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (i : ι) →
      Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), zCell i) (ρc i))
        ((0 : Euclidean (n - 1)), zCell i) (Rc i) (B i) (τlead i) (row i) (col i)
        (sourceDilation H.map σ),
    (∀ σ hσ i,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        ODE.IsSmoothFlowOn (liftedDirection (T i) (current σ hσ i).Q (row i) (col i))
          (0, ((0 : Euclidean (n - 1)), zCell i)) (Rc i) (Rc i / 2)
          (existenceTime (Rc i) (liftedLowBound (T i) (B i))) Ψ ∧
        (current σ hσ i).forward = forwardFromLift Ψ ∧
        (current σ hσ i).inverse = footpointFromLift Ψ ∧
        IsImmersionOn (sourceDilation H.map σ) U ∧
        HasFullNormalRankOn (sourceDilation H.map σ) U ∧
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δgeometry i ∧
        EqOn (current σ hσ i).forward (sourceTransportFlow (c₀ i).forward σ)
          (Ioo (-τlead i) (τlead i) ×ˢ
            ball ((0 : Euclidean (n - 1)), zCell i) (Rc i / 8)) ∧
        EqOn (current σ hσ i).inverse (sourceTransportFlow (c₀ i).inverse σ)
          (current σ hσ i).D ∧
        EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
          (sourceAmplitude ((c₀ i).scalar (fun _ ↦ 1)) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
            carrierNullvector (T i) (current σ hσ i).Q (col i) w)
          (sourceAmplitude (fun w ↦ (c₀ i).scalar (fun _ ↦ 1) w •
            carrierNullvector (T i) (c₀ i).Q (col i) w) σ)
          ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
        ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
          EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
            (fun w ↦ sourceAmplitude ((c₀ i).scalar (fun _ ↦ 1)) σ w *
              weight ((current σ hσ i).inverse (coordinates (adaptedCoordinates (T i).data.adapted) w)))
            ((coordinates (adaptedCoordinates (T i).data.adapted)) ⁻¹' (current σ hσ i).D)) ∧
      ∀ σ hσ, let current := current σ hσ
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
  obtain ⟨Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, cap, hcap, hcap8,
    current, hcurrent, hcarrier⟩ :=
    exists_finite_seed_source_density_carriers_with_normalized_actions
      H P hUG hbounded T hP Ω hΩ zCell ρc Rc B τlead L Mc row col
      hKΩ hΩpatch hRc hB hτeq hL hΩscale hbuffer hphysical c₀ htrans
      hMc hforward R hR hRT hRU hRtime V hV hVP hflow hlabel
      D hD z₀ ηb hηb r a r' a' hr hr' ha' hcell hrr haa har' haR hsupportD houter
      p₀ q₀ ρ τ hρ hτ W Bi hW hKiW hBi hWBi hBiDom hfoot It hIt hIIt hsegT hseg
      A ε gap hε hgap hfreq δgeometry hδgeometry hgeometry
  refine ⟨Cnorm, Cpdo, hCnorm, hCpdo, Bhigh, hBhigh, cap, hcap, hcap8,
    current, hcurrent, ?_⟩
  intro σ hσ current' v hv hpos hinterval hvnorm e d J u Ωi S
  obtain ⟨hsupport, hbsmooth, hA, Vop, hVop, _⟩ :=
    hcarrier σ hσ v hv hpos hinterval hvnorm
  exact ⟨hsupport, hbsmooth, hA, Vop, hVop⟩

end JanetCartan.ContinuumRow.NormalizedSelection
