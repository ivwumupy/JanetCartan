module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.InitializedDensityProducts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.PrescribedMeasuredSource.Raw

/-!
# Corrected raw inverse inside the original common initializer

The original initializer supplies the charts, density product regions and sharp
low reserve used by the prescribed-mask construction. Apply that construction
once, retaining the same source carriers, coercive inverse, inner exterior and
raw estimates for every admissible smooth physical density.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ContinuumInverse
open ContinuumRow.NormalizedSelection
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumNormal.SourceDensityLimitRealization
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

open PositiveReference PositiveReference.FlowConstruction

open ContinuumNormal ContinuumNormal.RetainedFrozen ContinuumNormal.FrozenModel
open ContinuumNormalReduction TransportSymbol CanonicalCarrier CanonicalConic
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open ContinuumAdjoint.Canonical.PhaseExtension CommonMeasurement
open CarrierSobolev

open TransportKernel CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- Apply the prescribed measured corrected-source inverse to the original
common initializer. All geometric inputs, original density labels, cutoffs and
source-scale continuations use its same witnesses. Prescribed extra spatial
caps and the buffered phase geometry are retained on this selection. Raw and
density bounds are chosen before the varying source scale and density. The
literal corrected test and adjoint actions identify this same operator for
the corrected-source consumer; no coercivity or regularity estimate is assumed
(`app:ch_background:prop:bg-inverse`,
`app:ch_background:prop:bg-adjoint`, `new:sec:order-of-choices`). -/
theorem exists_common_initializer_with_prescribed_corrected_source_raw_inverse
    {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ) (hD : D.IsValid c C),
      ∃ kCenter : Fin D.chartCount → Euclidean n,
        (∀ b, kCenter b ∈ sphere (0 : Euclidean n) 1) ∧
        (∀ b, kCenter b ∈ D.domain b) ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      (∀ i Q, ContDiffOn ℝ ∞ ((T i).family.flow Q).position
        (((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters)) ∧
      (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
        q.1 ∈ ball (0 : Euclidean n) b) ∧
      (∀ i, ∃ (Rinner : ℝ)
        (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
          (Euclidean n × (ℝ × Euclidean (n - 1)))),
        0 < Rinner ∧ Rinner < (T i).data.localReference.stateRadius ∧
        (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData)
            (3 * (T i).family.sourceRadius),
          ‖(A.symm : _ →L[ℝ] _).comp
              (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
            ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
        (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
          (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
            closedBall (0, (T i).data.center) Rinner) ∧
        (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
          cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
          ∀ z ∈ closedBall (0, (T i).data.center) Rinner,
            ⟪(normalizedHomogeneousSymbol isOpen_ball Q.1 Q.2.1).hp z,
              (T i).data.adapted.normal⟫_ℝ ≠ 0)) ∧
      ∃ γ > 0, (∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
          (T i).data.localReference.stateRadius,
        γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ|) ∧
      ∃ r : ℝ, 0 < r ∧ 3 * r < b ∧
        (∀ i, 3 * r < (T i).reference.radius) ∧
    ∃ εlead : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ, (∀ i, 0 < εlead i) ∧
    ∃ centers : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → Finset (parameterCube (D.patches i.1 i.2).radius),
    ∃ row col : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → Fin n,
    ∃ ρlead L τ Rc τc Mc rcomp δcomp σcover : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ,
      (∀ i j, 8 * rcomp i j ≤ Rc i j / 32) ∧
      (∀ i j, 0 < ρlead i j ∧ 0 < L i j ∧ 0 < τ i j ∧ 0 < Rc i j ∧ 0 < τc i j ∧
        0 < Mc i j ∧ 0 < rcomp i j ∧ 0 < δcomp i j ∧ 0 < σcover i j) ∧
    ∃ Ωc : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → Set (Euclidean n × Euclidean 3),
    ∃ ρc Bc gc μc Bfull : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ,
      (∀ i j,
        0 < μc i j ∧
        (∀ s ∈ Ioc (0 : ℝ) 1,
          MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (s • w.1, w.2)) (Ωc i j) (Ωc i j)) ∧
        closedBall ((0 : Euclidean n), j.1.1) (2 * ρc i j) ⊆ Ωc i j ∧
        closedBall ((0 : Euclidean n), j.1.1) (2 * ρc i j) ⊆
          (ball (0 : Euclidean n) (T i).physicalRadius ∩ interior (closedBall 0 b)) ×ˢ
            parameterInterior (3 * (D.patches i.1 i.2).radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), j.1.1) (2 * ρc i j))
          (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) ∧
        ∀ w ∈ closedBall ((0 : Euclidean n), j.1.1) (2 * ρc i j),
          2 * μc i j ≤ |(cubePencil ((D.patches i.1 i.2).toFun w.2)).adjugate (row i j) (col i j)|) ∧
      (∀ i j, let T := T i
        let z₀ := j.1.1
        let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
        0 < Bfull i j ∧
        τ i j = existenceTime (L i j)
          (LeadingWave.FullModulation.liftedLowBound T (Bfull i j)) / 4 ∧
        τ i j ≤ L i j / 16 ∧
        MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
          (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
            (z₀, T.reference.spatialPatch z₀))) (L i j)) (closedBall a (ρlead i j))) ∧
      (∀ (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) (j : centers i), let T := T i
        let P := D.patches i.1 i.2
        let K := closedBall (0 : Euclidean n) b
        let z₀ := j.1.1
        let Ωc := Ωc i j
        let ρc := ρc i j
        let Bc := Bc i j
        let gc := gc i j
        let Rc := Rc i j
        let τc := τc i j
        (0 < ρc ∧ 0 < Bc ∧ 0 < gc ∧ IsOpen Ωc ∧
          closedBall ((0 : Euclidean n), z₀) ρc ⊆ Ωc ∧
          Ωc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            parameterInterior (3 * P.radius / 2) ∧
          MapsTo Prod.fst (closedBall ((0 : Euclidean n), z₀) ρc)
            (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
          MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
            (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)), z₀)) Rc)
            (closedBall ((0 : Euclidean n), z₀) ρc) ∧
          τc = existenceTime Rc (NullTransport.ActualFlow.liftedLowBound T Bc) / 4 ∧
          τc ≤ Rc / 16)) ∧
    (∀ (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) (j : centers i), let T := T i
      let z₀ := j.1.1
      let a := ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀))
      closedBall a (2 * σcover i j) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ i j / 2) (τ i j / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
              (L i j / 64)) ∧
      closedBall a (2 * σcover i j) ⊆ closedBall a (ρlead i j) ∧
      ∀ w ∈ closedBall a (2 * σcover i j),
        w.2.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T)
          (min T.family.radius (3 * T.family.sourceRadius))) ∧
    ∃ εcarrier ρdet : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ,
      (∀ i j, 0 < εcarrier i j ∧ 0 < ρdet i j ∧
        let T := T i
        let z := j.1.1
        let cell := ball (0 : Euclidean n) (εcarrier i j) ×ˢ
          ball (z 0, spectatorCenter z) (εcarrier i j)
        let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, ContinuumRow.CanonicalCarrier.parameter p.2)
        MapsTo (ContinuumRow.LeadingPrimitive.carrierGraph T) cell
          (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (σcover i j)) ∧
        MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) cell
          (Ioo (-δcomp i j) (δcomp i j) ×ˢ ball ((0 : Euclidean (n - 1)), z) (rcomp i j)) ∧
        cell ⊆ (ball 0 R ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
          (ContinuumRow.CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * (D.patches i.1 i.2).radius)) ∧
        cell ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
          (ContinuumRow.CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * (D.patches i.1 i.2).radius / 2)) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) (ρdet i j))
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
        closedBall ((0 : Euclidean n), z) (ρdet i j) ⊆
          ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * (D.patches i.1 i.2).radius) ∧
        MapsTo ψ cell (closedBall ((0 : Euclidean n), z) (ρdet i j))) ∧
      (∀ i z, z ∈ parameterCube (D.patches i.1 i.2).radius → ∃ j : centers i,
        ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
          ball (0 : Euclidean n) (εcarrier i j) ×ˢ
            ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j)) ∧
    ∃ V : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (Euclidean 3 × Euclidean (n - 1)),
      (∀ i, IsOpen (V i) ∧
        (∀ z ∈ parameterCube (D.patches i.1 i.2).radius, (z, (T i).reference.spatialPatch z) ∈ V i) ∧
        (ball (0 : Euclidean n) (εlead i) ×ˢ V i ⊆
          ⋃ j : centers i, closedBall ((0 : Euclidean n),
            (j.1.1, (T i).reference.spatialPatch j.1.1)) (σcover i j))) ∧
    ∃ Mproduct Rproduct : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ,
      (∀ i j,
        let E := ball (0 : Euclidean n) (Rproduct i j) ×ˢ
          ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j)
        0 < Mproduct i j ∧ 0 < Rproduct i j ∧ Rproduct i j ≤ εcarrier i j ∧
        Rproduct i j ≤ (T i).physicalRadius ∧
        ball (0 : Euclidean n) (Rproduct i j) ⊆ ball 0 R ∧
        Rproduct i j ≤ L i j / (64 * Mproduct i j) ∧
        E ⊆ ball (0 : Euclidean n) (εcarrier i j) ×ˢ
          ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) ∧
        (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ E ↔
          ((0 : Euclidean n), z) ∈ ball (0 : Euclidean n) (εcarrier i j) ×ˢ
            ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j)) ∧
        ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) ⊆
          CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * (D.patches i.1 i.2).radius / 2) ∧
        MapsTo (densityCoordinates (T i)) E
          (outputCylinder ((0 : Euclidean (n - 1)), j.1.1) (Rc i j) (τc i j)) ∧
        (∀ p ∈ E, (densityCoordinates (T i) p).2 ∈
          closedBall ((0 : Euclidean (n - 1)), j.1.1) (L i j / 64)) ∧
        (∀ p ∈ E, |(densityCoordinates (T i) p).1| < L i j / (64 * Mproduct i j)) ∧
        ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (row' col' : Fin n)
          (current : Chart (T i) (Ωc i j)
            (closedBall ((0 : Euclidean n), j.1.1) (ρc i j))
            ((0 : Euclidean (n - 1)), j.1.1) (Rc i j) (Bc i j) (τc i j) row' col' F),
          cNorm (Icc (-τc i j) (τc i j) ×ˢ
            closedBall ((0 : Euclidean (n - 1)), j.1.1) (Rc i j / 8)) 1 current.forward ≤ Mproduct i j ∧
          MapsTo (densityCoordinates (T i)) E current.D ∧
          MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)) E
            (closedBall ((0 : Euclidean n), j.1.1) (ρc i j)) ∧
          ContDiffOn ℝ ∞ (densityFootpoint (T i) current.inverse) E ∧
          MapsTo (densityFootpoint (T i) current.inverse) E
            (ball ((0 : Euclidean (n - 1)), j.1.1) (L i j / 16)) ∧
          ∀ s ∈ Ioc (0 : ℝ) 1,
            MapsTo (densityFootpoint (T i) (sourceTransportFlow current.inverse s)) E
              (ball ((0 : Euclidean (n - 1)), j.1.1) (L i j / 16))) ∧
      (∀ i z, z ∈ parameterCube (D.patches i.1 i.2).radius → ∃ j : centers i,
        ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
          ball (0 : Euclidean n) (Rproduct i j) ×ˢ
            ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j)) ∧
      ∀ εframe : ℝ, 0 < εframe →
      ∀ (qext : BallExtension.Parameters (Euclidean n)),
        qext.center = 0 → qext.radius = b →
      ∀ (k : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Euclidean n),
        (∀ i, k i ≠ 0) → (∀ i, k i ∈ D.domain i.1) →
      let z := fun i : (j : Fin D.chartCount) × Fin (D.patchCount j) ↦
        D.roots i.1 i.2 (k i)
      ∃ (hz : ∀ i, z i ∈ parameterInterior (D.patches i.1 i.2).radius)
        (hinc : ∀ i, incidence (k i) ((D.patches i.1 i.2).toFun (z i)) = 0)
        (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i)
          ((D.patches i.1 i.2).toFun w)) (z i) (EuclideanSpace.single 0 1) ≠ 0),
    ∃ ρF ρT qrad s e cF bF cT bT : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
    ∃ VF LF : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (T i).family.radius / 8 ∧ 0 < e i ∧
        2 * qrad i ≤ ρF i ∧ 2 * qrad i ≤ ρT i ∧ e i ≤ ρF i ∧ e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ ρFext ρText qextRad sext eext cFext bFext cText bText : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
    ∃ VFext LFext : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (ℝ × Euclidean (n - 1)),
    ∃ VText LText : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρFext i ∧ 0 < ρText i ∧ 0 < qextRad i ∧ 0 < sext i ∧ sext i ≤ qextRad i ∧
        3 * qextRad i < (T i).family.radius / 8 ∧ 0 < eext i ∧
        4 * qextRad i ≤ ρFext i ∧ 4 * qextRad i ≤ ρText i ∧ 2 * eext i ≤ ρFext i ∧ 2 * eext i ≤ ρText i ∧
        0 < cFext i ∧ 0 < bFext i ∧ 0 < cText i ∧ 0 < bText i ∧
        IsOpen (VFext i) ∧ IsCompact (closure (VFext i)) ∧ IsCompact (LFext i) ∧ LFext i ⊆ VFext i ∧
        IsOpen (VText i) ∧ IsCompact (closure (VText i)) ∧ IsCompact (LText i) ∧ LText i ⊆ VText i) ∧
    ∃ ψF χF : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → FullQuotientInput n → ℝ,
    ∃ ψT χT : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → TransverseQuotientInput n → ℝ,
      (∀ i,
        let η := (T i).data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
        ContDiff ℝ ∞ (ψF i) ∧ HasCompactSupport (ψF i) ∧
        tsupport (ψF i) ⊆ ball (fullForwardCenter (z i) η) (ρFext i) ∧
        ContDiff ℝ ∞ (ψT i) ∧ HasCompactSupport (ψT i) ∧
        tsupport (ψT i) ⊆ ball (transverseForwardCenter (z i) η) (ρText i) ∧
        ContDiff ℝ ∞ (χF i) ∧ HasCompactSupport (χF i) ∧
        tsupport (χF i) ⊆ interior (fullParameterBox (z i) (sext i / 2) (eext i)) ×ˢ VFext i ∧
        ContDiff ℝ ∞ (χT i) ∧ HasCompactSupport (χT i) ∧
        tsupport (χT i) ⊆ interior (transversePrimitiveBox (z i) (sext i / 2) (eext i)) ×ˢ VText i) ∧
    ∃ εtransport : ℝ, ∃ gtransport : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ, 0 < εtransport ∧ (∀ i, 0 < gtransport i) ∧
    ∃ transportCenters : (i : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → Finset (parameterCube (D.patches i.1 i.2).radius),
    ∃ transportRow transportCol : (i : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → transportCenters i → Fin n,
    ∃ ρtransport Ltransport : (i : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → transportCenters i → ℝ,
    ∃ hρtransport : ∀ i q, 0 < ρtransport i q,
    ∃ Ωtransport : (i : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → transportCenters i → Set (Euclidean n × Euclidean 3),
      (∀ i q, 0 < Ltransport i q ∧ IsOpen (Ωtransport i q) ∧
        closedBall ((0 : Euclidean n), q.1.1) (ρtransport i q) ⊆ Ωtransport i q ∧
        Ωtransport i q ⊆ (ball (0 : Euclidean n) (T i).physicalRadius ∩
          interior (closedBall 0 b)) ×ˢ parameterInterior (3 * (D.patches i.1 i.2).radius / 2)) ∧
      (∀ i, closedBall (0 : Euclidean n) εtransport ×ˢ parameterCube (D.patches i.1 i.2).radius ⊆
        ⋃ q, closedBall ((0 : Euclidean n), q.1.1)
          (transportExtensionRadius ((0 : Euclidean n), q.1.1) (hρtransport i q))) ∧
    ∃ Dq Dt : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℕ → ℝ, (∀ i m, 0 < Dq i m) ∧ (∀ i m, 0 < Dt i m) ∧
    ∃ εcommon : ℝ, 0 < εcommon ∧ εcommon < r ∧
      (∀ i,
        (ball (0 : Euclidean n) εcommon ×ˢ V i ⊆
          ⋃ j : centers i, closedBall ((0 : Euclidean n),
            (j.1.1, (T i).reference.spatialPatch j.1.1)) (σcover i j)) ∧
        (closedBall (0 : Euclidean n) εcommon ×ˢ parameterCube (D.patches i.1 i.2).radius ⊆
          ⋃ q, closedBall ((0 : Euclidean n), q.1.1)
            (transportExtensionRadius ((0 : Euclidean n), q.1.1) (hρtransport i q)))) ∧
      ∀ (p : BallExtension.Parameters (Euclidean n))
        (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ),
        (∀ j ∈ orders, 0 < margin j) →
        (∀ j ∈ orders, 0 < extendedMargin j) →
        ∀ cap : ℝ, 0 < cap →
      ∃ θ : ℝ, 0 < θ ∧ θ < cap ∧ θ ≤ 1 ∧
      ∃ H : FlatReference n, H.domain = G₀.domain ∧ H.map = sourceDilation G₀.map θ ∧
      (∃ seed : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → (j : centers i) →
        PositiveReference.FlowConstruction.Chart (T i) (Ωc i j)
          (closedBall ((0 : Euclidean n), j.1.1) (ρc i j))
          ((0 : Euclidean (n - 1)), j.1.1) (Rc i j) (Bc i j) (τc i j)
          (row i j) (col i j) H.map,
        (∀ i j, cNorm (Icc (-τc i j) (τc i j) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), j.1.1) (Rc i j / 8))
            1 (seed i j).forward ≤ Mc i j) ∧
        (∀ i j, (seed i j).Q.1 0 = cubeStress n ∧
          ∀ q ∈ closedBall (0, (T i).data.center) (T i).data.localReference.stateRadius,
            ⟪(normalizedHomogeneousSymbol isOpen_ball (seed i j).Q.1
              (seed i j).Q.2.1).hp q, (T i).data.adapted.normal⟫_ℝ ≠ 0) ∧
        (∀ incidenceCap : ℝ, 0 < incidenceCap →
        let Tm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) ↦ T ⟨b, l⟩
        let Im : (b : Fin D.chartCount) → Fin (D.patchCount b) → Type :=
          fun b l ↦ ↥(centers ⟨b, l⟩)
        let Rm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
          Rproduct ⟨b, l⟩ j
        let Vm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
          ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier ⟨b, l⟩ j)
        let rowm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
          row ⟨b, l⟩ j
        let colm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
          col ⟨b, l⟩ j
        let c₀ := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦
          seed ⟨b, l⟩ j
        let Ωm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ Ωc ⟨b, l⟩ j
        let zCellm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ j.1.1
        let ρcm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ ρc ⟨b, l⟩ j
        let Rcm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ Rc ⟨b, l⟩ j
        let Mm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ Bc ⟨b, l⟩ j
        let τleadm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ τc ⟨b, l⟩ j
        let Lm := fun (b : Fin D.chartCount) (l : Fin (D.patchCount b)) (j : Im b l) ↦ L ⟨b, l⟩ j
        ∀ aExtra : (p : IncidenceCenter D) → (l : Fin (D.patchCount p.1.1)) →
          Im p.1.1 l → {ε : ℝ // 0 < ε},
        let E := fun b l j ↦ ball (0 : Euclidean n) (Rm b l j) ×ˢ Vm b l j
        ∃ cell : (p : IncidenceCenter D) → (a : Fin (D.patchCount p.1.1)) → Im p.1.1 a,
          (∀ p a, ((0 : Euclidean n),
            (D.roots p.1.1 a p.1.2 0, spectatorCenter (D.roots p.1.1 a p.1.2))) ∈
              E p.1.1 a (cell p a)) ∧
        ∃ centers : Finset (IncidenceCenter D), ∃ εcover : centers → ℝ,
          (∀ j, 0 < εcover j) ∧
          sphere (0 : Euclidean n) 1 ⊆ ⋃ j : centers, ball j.1.1.2 (εcover j) ∧
          (∀ j, ball j.1.1.2 (εcover j) ⊆ D.domain j.1.1.1) ∧
          (∀ j, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ s : Euclidean n,
            c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil q) s‖ ^ 2 +
              ∑ a, inner ℝ (CubeCarrier.quadratic ((D.patches j.1.1.1 a).toFun
                (D.roots j.1.1.1 a q))) s ^ 2) ∧
        let ι := (j : centers) × Fin (D.patchCount j.1.1.1)
        let family := fun i : ι ↦ Tm i.1.1.1.1 i.2
        let z := fun i : ι ↦ D.roots i.1.1.1.1 i.2 i.1.1.1.2
        let k := fun i : ι ↦ i.1.1.1.2
        ∃ t r a r' a' : ι → ℝ,
        ∃ (_ht : ∀ i, 0 < t i) (_hr : ∀ i, 0 < r i) (_ha : ∀ i, 0 < a i)
          (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i),
        ∃ hcell : ∀ i, 4 * a' i < 1 / 2,
        let ηb := fun i ↦ (family i).data.adapted.embedding.toContinuousLinearMap.adjoint (t i • k i)
        ∃ hηb : ∀ i, ηb i ≠ 0,
          (∀ i, ‖t i • k i‖ = 1 / 4) ∧
          (∀ i, NormedSpace.normalize (t i • k i) = NormedSpace.normalize (k i)) ∧
          (∀ i, a' i ≤ (aExtra i.1.1 i.2 (cell i.1.1 i.2)).1) ∧
          (∀ i, 6 * a i < incidenceCap ∧
            coefficientDomain (z i) (r i) (6 * a i) ⊆ E i.1.1.1.1 i.2 (cell i.1.1 i.2) ∧
            r' i ≤ r i ∧ a' i ≤ a i ∧ a' i ≤ r' i ∧ 6 * a i < (family i).family.radius) ∧
          (∀ j : centers, ∀ q ∈ ball j.1.1.2 (εcover j), ∀ l : Fin (D.patchCount j.1.1.1),
            ((0 : Euclidean n), (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))) ∈
              E j.1.1.1 l (cell j.1 l) ∧
            angularMask (z ⟨j, l⟩) (NormedSpace.normalize (ηb ⟨j, l⟩))
              (ha' ⟨j, l⟩) (angularWidth_spec (hηb ⟨j, l⟩) (hr' ⟨j, l⟩)).1
              (D.roots j.1.1.1 l q 0, spectatorCenter (D.roots j.1.1.1 l q))
              (NormedSpace.normalize ((family ⟨j, l⟩).data.adapted.embedding.toContinuousLinearMap.adjoint q)) = 1) ∧
        ∃ b : ℝ, ∃ (_hb : 0 < b) (_hbcell : 4 * b < 1 / 2),
          6 * b < H.domain.chartRadius ∧ 6 * b < 1 / 2 ∧ (∀ i, 6 * b < a' i) ∧
        (∀ i : ι,
          IsCompact (parameter '' carrierSupport (z i) (r := a' i)) ∧
          MapsTo parameter (carrierSupport (z i) (r := a' i))
            (parameterInterior (D.patches i.1.1.1.1 i.2).radius) ∧
          (∀ z' ∈ parameter '' carrierSupport (z i) (r := a' i),
            ∀ θ ∈ closedDirections (ηb i) (r' i),
              NormedSpace.normalize (Sampling.frozenInputCovector (family i) z' θ) ∈
                D.domain i.1.1.1.1) ∧
          ∀ detector : Euclidean (n - 1) → ℂ,
            (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections (ηb i) (r' i)) →
            (∀ z' ∈ parameter '' carrierSupport (z i) (r := a' i),
              ∀ θ ∈ Sampling.detectorDirectionSupport detector,
                NormedSpace.normalize (Sampling.frozenInputCovector (family i) z' θ) ∈
                  D.domain i.1.1.1.1) ∧
            IsCompact (Sampling.transverseDetectorIncidenceSupport (family i)
              (parameter '' carrierSupport (z i) (r := a' i)) detector) ∧
            ∀ w ∈ Sampling.transverseDetectorIncidenceSupport (family i)
                (parameter '' carrierSupport (z i) (r := a' i)) detector,
              w.1 ∈ parameterInterior (D.patches i.1.1.1.1 i.2).radius ∧ w.2 ≠ 0 ∧
              incidence w.2 ((D.patches i.1.1.1.1 i.2).toFun w.1) = 0 ∧
              fderiv ℝ (fun z' ↦ incidence w.2 ((D.patches i.1.1.1.1 i.2).toFun z')) w.1
                (EuclideanSpace.single 0 1) ≠ 0) ∧
        ∃ δ > (0 : ℝ),
        ∃ Dc : ι → CoefficientNormCharts n,
        ∃ p₀ : ι → InputVariables n, ∃ q₀ : ι → Variables n × Euclidean 2,
        ∃ ρ τ : ι → ℝ, ∃ W Bi : ι → Set (InputVariables n), ∃ It : ι → Set ℝ,
        ∃ A : ι → InputVariables n ≃L[ℝ] Variables n × Euclidean 2,
        ∃ ε gap : ι → ℝ, ∃ Qc Ωi : ι → Set (Variables n × Euclidean 2),
        ∃ βphase cJphase : ι → ℝ,
        ∃ Vphase Lphase : ι → Set (ℝ × Euclidean (n - 1)),
        ∃ Gphase : ι → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
        (∀ i : ι,
        let T := family i
        let P := D.patches i.1.1.1.1 i.2
        let z₀ := z i
        let ηb := ηb i
        let r := r i
        let a := a i
        let r' := r' i
        let a' := a' i
        let ha' := ha' i
        let E := E i.1.1.1.1 i.2 (cell i.1.1 i.2)
        let D := Dc i
        let p₀ := p₀ i
        let q₀ := q₀ i
        let ρ := ρ i
        let τ := τ i
        let W := W i
        let Bi := Bi i
        let It := It i
        let A := A i
        let ε := ε i
        let gap := gap i
        let Qc := Qc i
        let Ωi := Ωi i
        let β := βphase i
        let cJ := cJphase i
        let Vphase := Vphase i
        let Lphase := Lphase i
        let G := Gphase i;
          (p₀ = augmentedInputCenter T (z₀ := z₀) (k := t i • k i) ∧
          q₀ = frozenAugmentedChart T p₀ ∧ 6 * a ≤ r ∧ 4 * a < 1 / 2 ∧
          (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
            carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
          r' ≤ ρ ∧ 4 * a' < ρ ∧ 0 < β ∧ 0 < cJ ∧ IsOpen Vphase ∧
          IsCompact (closure Vphase) ∧ IsCompact Lphase ∧ Lphase ⊆ Vphase) ∧
          originOutput q₀ = q₀ ∧
          Qc = compactTarget (1 / 4) q₀ τ ∧ Ωi = conicTarget (1 / 4) q₀ τ ∧
          0 < ρ ∧ 0 < τ ∧ IsOpen W ∧ closedBall p₀ ρ ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧
          Bi ⊆ symbolInputDomain z₀ ηb r (6 * a) ∧ D.field.region ⊆ E ∩ coefficientDomain z₀ r (6 * a) ∧
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
          ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F (ball 0 R))
            (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
            ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (projectedStress F - fun _ ↦ cubeStress n) < δ →
            let Q := ⟨projectedStress F,
              contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow⟩
            (ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
              (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
            (∀ p ∈ physicalParameterSet z₀ (6 * a), ∀ u ∈ dataBox z₀ ηb (2 * r),
              ‖G.symm.toContinuousLinearMap.comp
                (fderiv ℝ (adaptedTransportChart T Q p) u) -
                ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
            BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
              (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) Vphase Lphase β cJ G ∧
            (∀ p ∈ physicalParameterSet z₀ (6 * a),
              ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
                ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) ∧
            closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
            MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
              (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
            (∀ p ∈ closedBall p₀ ρ,
              ‖A.symm.toContinuousLinearMap.comp
                (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
                ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
            (closure (augmentedTransportGradient (transportPosition T Q) '' conicMaskSupport z₀ ηb r' a') ∩
              {p | p.1.2.2 ≠ 0} ⊆ symbolDomain T Q z₀ ηb r (6 * a)) ∧
            (∀ x : Variables n, ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
              (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
                conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
            (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
              ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
            (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a) ∧
            MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
              (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
            (∀ p ∈ closedBall p₀ ρ,
              ‖A.symm.toContinuousLinearMap.comp
                (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q 0)) p) -
                ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
            (∀ x : Variables n, ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
              (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
                conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
            (closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
              conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
              frozenSymbolDomain T Q z₀ ηb r (6 * a)))) ∧
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
        ∃ χinitial : ι → ContDiffBump (0 : CarrierVariable n),
        ∃ rMeasure : ℝ, ∃ hrMeasure : 0 < rMeasure, ∃ hMeasureCell : 4 * rMeasure < 1 / 2,
          6 * rMeasure < b ∧ 6 * rMeasure < H.domain.chartRadius ∧
          6 * rMeasure < 1 / 2 ∧ (∀ i, 6 * rMeasure < a' i) ∧
        ∃ χcoeff : Euclidean n → ℝ,
          ContDiff ℝ ∞ χcoeff ∧ (∀ x, χcoeff x ∈ Icc (0 : ℝ) 1) ∧
          HasCompactSupport χcoeff ∧ tsupport χcoeff ⊆ ball 0 (5 * rMeasure) ∧
          closedBall 0 (4 * rMeasure) ⊆ interior {x | χcoeff x = 1} ∧
        ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
        ∃ coeff : ℝ → ReducedCoefficientIndex n → C(Torus n, ℝ),
        ∃ Cimage Cbound Lbound : ℕ → ℝ,
          (∀ m, 0 < Cimage m) ∧ (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
          (∀ σ j, IsSmoothPeriodic (coeff σ j)) ∧
          (∀ j x, coeff 0 j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
            ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
              (AmplitudeBound.centeredTorusRepresentative x) j) ∧
          (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ j x,
            coeff σ j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
              geometricReducedCoefficients (sourceDilation H.map σ)
                (AmplitudeBound.centeredTorusRepresentative x) j) ∧
          (∀ m σ, σ ∈ Ioc (0 : ℝ) σ₀ → ∀ j x,
            ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j - coeff 0 j)) x‖ ≤ Cimage m * σ ∧
            ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j)) x‖ ≤ Cimage m) ∧
        let χ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 1
        let χsrc := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 2
        let ψ := FixedCutoffs.periodic (n := n) hrMeasure hMeasureCell 0
        let selected := fun i : ι ↦ cell i.1.1 i.2
        let seed := fun i : ι ↦ c₀ i.1.1.1.1 i.2 (selected i)
        let rowi := fun i : ι ↦ rowm i.1.1.1.1 i.2 (selected i)
        let coli := fun i : ι ↦ colm i.1.1.1.1 i.2 (selected i)
        let angular := fun i ↦ angularMask (z i) (NormedSpace.normalize (ηb i))
          (ha' i) (angularWidth_spec (hηb i) (hr' i)).1
        (∀ σ ∈ Ioc (0 : ℝ) σ₀,
        let d := fun i ↦ normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
          (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i) (angular i)
          FixedCutoffs.highFrequency σ
        let e := fun i ↦ normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
          (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell (angular i)
          FixedCutoffs.highFrequency σ
        (∀ i, MapsTo (fun p : Euclidean n × CarrierParameter ↦
          (p.2, normalizedTransportPosition (family i) (seed i).Q σ p))
          (closedBall 0 (6 * rMeasure) ×ˢ carrierSupport (z i) (r := a' i))
          (interior {q | χinitial i q = 1})) ∧
        ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ i w, (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
        let Uop := fun i ↦ restrictCarrier χ (Vop i);
          (∀ i, ‖Uop i‖ ≤ ‖Vop i‖) ∧
          (∀ i w, (Uop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
          (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) → B = Uop i) ∧
          (∀ i, (∀ f : carrierInitialTestSpace n,
              Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (d i) f.val) →
            ∀ f : carrierInitialTestSpace n,
              Uop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
          augmentedNormal (imageChannel (coeff σ) χ χsrc) Uop ψ =
            imageChannel (coeff σ) χ χsrc ∘L (imageChannel (coeff σ) χ χsrc).adjoint +
              (∑ i, cutoffMultiplier χ ∘L
                (carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint) ∘L cutoffMultiplier χ) +
              cutoffMultiplier ((1 - ψ) ^ 2) ∧
          ∀ selectedCoeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
            (∀ j x, selectedCoeff j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
              geometricReducedCoefficients (sourceDilation H.map σ)
                (AmplitudeBound.centeredTorusRepresentative x) j) →
          ∀ B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i w, (B i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) →
            let A := augmentedRow (imageChannel selectedCoeff χ χsrc) B ψ
            (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
              A.adjoint w ∈ augmentedInputLevel n ι s ∧
              (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
                Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) ∧
            ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
              let u := A.adjoint w
              ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
                (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
                  (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                    (angularWidth_spec (hηb i) (hr' i)).1 (u.fst.snd i) (hf i))) ∧
                  MemPhysicalSobolev s (physicalComplexifyL2
                  (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                    (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (u.fst.snd i) (hf i)))) ∧
                densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                  (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s u ≤
                  Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) ∧
                densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                  (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s u ≤
                  Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖)) ∧
        (∀ ψcorrected : C(Torus n, ℝ), IsSmoothPeriodic ψcorrected →
        ∃ Ccorrected Lcorrected : ℕ → ℝ,
          (∀ s, 0 ≤ Ccorrected s) ∧ (∀ s, 0 ≤ Lcorrected s) ∧
        ∀ σ ∈ Ioc (0 : ℝ) σ₀,
        ∀ vDensity : ι → CarrierVariable n → ℝ,
          (∀ i, ContDiff ℝ ∞ (vDensity i)) →
          (∀ i q, 1 + vDensity i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zCellm i.1.1.1.1 i.2 (selected i))
            (Lm i.1.1.1.1 i.2 (selected i) / 8)) (2 * (n + 1) + 14)
              (PositiveBackground.densityOnInitialLabels (vDensity i)) ≤ 1) →
        let Hhigh := fun s ↦ 1 + ∑ i,
          cNorm (closedBall ((0 : Euclidean (n - 1)), zCellm i.1.1.1.1 i.2 (selected i))
            (Lm i.1.1.1.1 i.2 (selected i) / 8)) (s + 2 * (n + 1) + 14)
              (PositiveBackground.densityOnInitialLabels (vDensity i))
        let d := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
          (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
            (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i) (angular i)
            FixedCutoffs.highFrequency σ) (vDensity i)
        let e := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
          (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
            (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell (angular i)
            FixedCutoffs.highFrequency σ) (vDensity i)
        ∃ Vcorrected : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ i w, (Vcorrected i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) ∧
        let Ucorrected := fun i ↦ restrictCarrier χ (Vcorrected i);
          (∀ i w, (Ucorrected i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
          (∀ i, ∀ B : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ w, B.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) → B = Ucorrected i) ∧
          ∀ selectedCoeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
            (∀ j x, selectedCoeff j x = χcoeff (AmplitudeBound.centeredTorusRepresentative x) *
              geometricReducedCoefficients (sourceDilation H.map σ)
                (AmplitudeBound.centeredTorusRepresentative x) j) →
          ∀ B : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i w, (B i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) →
            let A := augmentedRow (imageChannel selectedCoeff χ χsrc) B ψcorrected
            (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
              A.adjoint w ∈ augmentedInputLevel n ι s ∧
              (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
                Ccorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + Hhigh s * ‖w‖)) ∧
            ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
              let u := A.adjoint w
              ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
                (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
                  (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                    (angularWidth_spec (hηb i) (hr' i)).1 (u.fst.snd i) (hf i))) ∧
                  MemPhysicalSobolev s (physicalComplexifyL2
                  (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                    (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (u.fst.snd i) (hf i)))) ∧
                densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                  (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s u ≤
                  Lcorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖) ∧
                densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                  (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s u ≤
                  Lcorrected s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖)) ∧
        let Ωflow := fun i : ι ↦ Ωm i.1.1.1.1 i.2 (selected i)
        let zScalar := fun i : ι ↦ zCellm i.1.1.1.1 i.2 (selected i)
        let ρflow := fun i : ι ↦ ρcm i.1.1.1.1 i.2 (selected i)
        let Rcflow := fun i : ι ↦ Rcm i.1.1.1.1 i.2 (selected i)
        let Bflow := fun i : ι ↦ Mm i.1.1.1.1 i.2 (selected i)
        let τflow := fun i : ι ↦ τleadm i.1.1.1.1 i.2 (selected i)
        let Lscalar := fun i : ι ↦ Lm i.1.1.1.1 i.2 (selected i)
        ∃ Cnorm Cpdo : ι → ℝ, (∀ i, 0 < Cnorm i) ∧ (∀ i, 0 < Cpdo i) ∧
        ∃ Bhigh : ι → ℕ → ℝ, (∀ i p, 0 < Bhigh i p) ∧
        ∃ densityCap > (0 : ℝ), densityCap ≤ σ₀ ∧ densityCap ≤ 1 / 8 ∧
        ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) densityCap → (i : ι) →
          Chart (family i) (Ωflow i) (closedBall ((0 : Euclidean n), zScalar i) (ρflow i))
            ((0 : Euclidean (n - 1)), zScalar i) (Rcflow i) (Bflow i) (τflow i) (rowi i) (coli i)
            (sourceDilation H.map σ),
        (∀ σ hσ i,
          ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
              ℝ × (Euclidean (n - 1) × Euclidean 3),
            ODE.IsSmoothFlowOn (NullTransport.ActualFlow.liftedDirection (family i) (current σ hσ i).Q (rowi i) (coli i))
              (0, ((0 : Euclidean (n - 1)), zScalar i)) (Rcflow i) (Rcflow i / 2)
              (existenceTime (Rcflow i) (NullTransport.ActualFlow.liftedLowBound (family i) (Bflow i))) Ψ ∧
            (current σ hσ i).forward = forwardFromLift Ψ ∧
            (current σ hσ i).inverse = footpointFromLift Ψ ∧
            IsImmersionOn (sourceDilation H.map σ) (ball 0 R) ∧
            HasFullNormalRankOn (sourceDilation H.map σ) (ball 0 R) ∧
            cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
              ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δ ∧
            EqOn (current σ hσ i).forward (sourceTransportFlow (seed i).forward σ)
              (Ioo (-τflow i) (τflow i) ×ˢ
                ball ((0 : Euclidean (n - 1)), zScalar i) (Rcflow i / 8)) ∧
            EqOn (current σ hσ i).inverse (sourceTransportFlow (seed i).inverse σ)
              (current σ hσ i).D ∧
            EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
              (sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ)
              ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
            EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
                carrierNullvector (family i) (current σ hσ i).Q (coli i) w)
              (sourceAmplitude (fun w ↦ (seed i).scalar (fun _ ↦ 1) w •
                carrierNullvector (family i) (seed i).Q (coli i) w) σ)
              ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
            ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
              EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
                (fun w ↦ sourceAmplitude ((seed i).scalar (fun _ ↦ 1)) σ w *
                  weight ((current σ hσ i).inverse (coordinates (adaptedCoordinates (family i).data.adapted) w)))
                ((coordinates (adaptedCoordinates (family i).data.adapted)) ⁻¹' (current σ hσ i).D)) ∧
          (∀ σ hσ, let current := current σ hσ
          ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
          (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
          (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
          (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
            1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8))
            (2 * (n + 1) + 14) (v i) ≤ 1) →
          let e := fun i ↦ data (family i) (current i).Q (sourceDilation H.map σ) (rowi i) (coli i)
            (current i).forward (current i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
            (ha' i) (hcell i)
            (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
            FixedCutoffs.highFrequency
          let d := fun i ↦ coefficientsOfCarrier (e i) (FixedCutoffs.physical (ha' i) 1)
          let J := fun i ↦ symbolJacobian (family i) (current i).Q
          let u := fun i ↦ symbolInverse (family i) (current i).Q (z i) (ηb i) (r i) (6 * a i)
          let Ωi := fun i ↦ symbolDomain (family i) (current i).Q (z i) (ηb i) (r i) (6 * a i)
          let S := fun i ↦ closedBall (spectatorCenter (z i)) (a' i / 2)
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
                (vectorTwoPositionL2Operator (by have := (rowi i).isLt; omega) (4 * (a' i))
                  (fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i)) (hbsmooth i)
                  (fullReflectedMatrixAmplitude_supportedInCenteredBox (d i) (J i) (u i) (Ωi i) (S i) (4 * (a' i)) (hsupport i))
                  (Cpdo i) (fun l j ξ is his ↦ (hA i) l j ξ is (by omega)))) ∧
            (∀ p l j, HasAmplitudeDerivativeBound
              (fun ξ z ↦ fullReflectedMatrixAmplitude (d i) (J i) (u i) (Ωi i) (S i) ξ z l j) p
              ((Bhigh i) p * (1 + cNorm (closedBall ((0 : Euclidean (n - 1)), (zScalar i)) ((Lscalar i) / 8)) p (v i)))) ∧
            ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < (a' i) →
              let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
              let Vb := CommonMeasurement.restrictCarrier χ (Vop i)
              let eb := data (family i) (current i).Q (sourceDilation H.map σ) (rowi i) (coli i) (current i).forward (current i).inverse
                (fun q ↦ positiveDensityAmplitude σ ((v i) q)) hb hbcell
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i) (angularWidth_spec (hηb i) (hr' i)).1)
                FixedCutoffs.highFrequency
              let db := coefficientsOfCarrier eb (FixedCutoffs.physical hb 1)
              let Aop := vectorTwoPositionL2Operator (by have := (rowi i).isLt; omega) (4 * (a' i))
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
            let unit := normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
              (seed i).forward (seed i).inverse (fun _ ↦ 1) (ha' i) (hcell i)
              (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
            let normalized := weightNormal unit
              (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (family i) (current i).inverse p)))
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
              let unitb := normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
                (seed i).forward (seed i).inverse (fun _ ↦ 1) hb hbcell
                (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                  (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency σ
              let normalizedb := weightNormal unitb
                (fun p ↦ Real.sqrt (1 + v i (densityFootpoint (family i) (current i).inverse p)))
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
                  Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral unitb f.val)) ∧
        (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) densityCap) i,
          RetainedFrozen.UnitRealization.UnitCarrierOutput (family i) (current σ hσ i).Q H.map
            (rowi i) (coli i) (seed i).forward (seed i).inverse (z i) (ηb i) (r i) (a i) (r' i) (a' i)
            (hr' i) (ha' i) (hcell i) (hηb i) (2 * (n + 1)) le_rfl) ∧
        InitializedFrozenSeedGap family (fun i ↦ (seed i).Q) H.map rowi coli
          (fun i ↦ (seed i).forward) (fun i ↦ (seed i).inverse) z ηb r' a'
          hr' ha' hcell hηb zScalar Lscalar ∧
        let Qcurrent : (i : ι) → ℝ → {QF : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ QF (ball 0 R) ∧ cNorm (closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius) 6
            (QF - fun _ ↦ cubeStress n) < (family i).family.threshold} := fun i σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) densityCap
          then (current σ hσ i).Q else (seed i).Q
        let μ := 2 * (n + 1)
        let angular := fun i ↦ angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
          (angularWidth_spec (hηb i) (hr' i)).1
        let d := fun i σ ↦ TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse (fun _ ↦ 1)
            (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency σ) (FixedCutoffs.physical (ha' i) 1)
        let J := fun i σ ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (family i))
          (normalizedTransportPosition (family i) (seed i).Q σ)
        let u := fun i σ ↦ if σ = 0 then frozenSymbolInverse (family i) (seed i).Q (z i) (ηb i) (r i) (6 * a i)
          else symbolInverse (family i) (Qcurrent i σ) (z i) (ηb i) (r i) (6 * a i)
        let S := fun i ↦ closedBall (spectatorCenter (z i)) (a' i / 2)
        let b := fun i σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
          fullReflectedMatrixAmplitude
            {d i σ with normal := fun p ↦ Real.sqrt (1 + v
              (sourceDensityFootpointExtension (family i) (seed i).inverse (σ, p))) • (d i σ).normal p}
            (J i σ) (u i σ) (Ωi i) (S i)
        let eZero : ι → (Euclidean (n - 1) × Euclidean 3 → ℝ) → CarrierData n (embeddingDimension n) :=
          fun (i : ι) (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
          SourceDensityLimitRealization.weightNormal (n := n) (N := embeddingDimension n)
            (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i) (seed i).forward (seed i).inverse
              (fun _ ↦ 1) (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency 0)
            (fun p : Euclidean n × CarrierParameter ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension (family i) (seed i).inverse (0, p))))
        (let image := FrozenImageComparison.fixedPeriodicChannel hrMeasure hMeasureCell
            (FrozenCoercivity.frozenImageArrays (projectedStress H.map 0))
        ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
        ∃ Mlimit ≥ (0 : ℝ), rInner ≤ rMeasure ∧
          0 < NormalAugmentation.globalGap g Mlimit ∧
          ∃ sourceCap > (0 : ℝ), ∃ hcapSource : sourceCap ≤ densityCap,
            sourceCap ≤ σ₀ ∧ sourceCap ≤ 1 ∧
          ∃ Cell Kraw Cfull Dfull Kpositive Cpositive Dpositive : ℕ → ℝ,
            (∀ s, 0 ≤ Cell s) ∧ (∀ s, 0 ≤ Kraw s) ∧
            (∀ s, 0 ≤ Cfull s) ∧ (∀ s, 0 ≤ Dfull s) ∧
          (∀ s, 0 ≤ Kpositive s) ∧ (∀ s, 0 ≤ Cpositive s) ∧
          (∀ s, 0 ≤ Dpositive s) ∧
          ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
          (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
          (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
          (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
            1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8)) (μ + 14) (v i) ≤ 1) →
          ∃ Vzero : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i,
              (∀ f : carrierInitialTestSpace n,
                Vzero i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) ∧
              (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eZero i (v i)) f) 2 (carrierMeasure n) ∧
                (Vzero i).adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (eZero i (v i)) f) ∧
              (∀ Wzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ f : carrierInitialTestSpace n,
                  Wzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) →
                  Wzero = Vzero i)) ∧
            let Wzero := fun i ↦ restrictCarrier χ (Vzero i)
            ‖physicalRow image Wzero‖ ≤ Mlimit ∧
            (∀ w : OutputL2 n,
              (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
              g * ‖w‖ ^ 2 ≤ ‖(physicalRow image Wzero).adjoint w‖ ^ 2) ∧
            (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
              inner ℝ (augmentedNormal image Wzero (innerCutoff hrInner hInnerCell) w) w) ∧
            (∀ w : OutputL2 n, NormalAugmentation.globalGap g Mlimit * ‖w‖ ^ 2 ≤
              ‖(augmentedRow image Wzero (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
            (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
              centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
                exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) ∧
            ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) sourceCap),
            let cσ := current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
            let e : ι → CarrierData n (embeddingDimension n) := fun i ↦
              data (family i) (cσ i).Q (sourceDilation H.map σ) (rowi i) (coli i)
                (cσ i).forward (cσ i).inverse (fun q ↦ positiveDensityAmplitude σ (v i q))
                (ha' i) (hcell i) (angular i) FixedCutoffs.highFrequency
            ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
              (∀ Wop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ i f, Wop i (carrierInitialTestToLp f) =ᵐ[volume]
                  carrierTestIntegral (e i) f.val) → Wop = Vop) ∧
              (∀ i,
                (∀ f : carrierInitialTestSpace n,
                  Vop i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (e i) f.val) ∧
                (∀ w : ComplexOutputL2 n,
                  MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
                  (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w)) ∧
              let imageCurrent := imageChannel (coeff σ) χ χsrc
              let Wcurrent := fun i ↦ restrictCarrier χ (Vop i)
              ‖physicalRow imageCurrent Wcurrent‖ ≤ Real.sqrt
                (Mlimit ^ 2 + min g (NormalAugmentation.globalGap g Mlimit) / 2) ∧
              (∀ w : OutputL2 n,
                (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
                (g / 2) * ‖w‖ ^ 2 ≤ ‖(physicalRow imageCurrent Wcurrent).adjoint w‖ ^ 2) ∧
              (∀ w : OutputL2 n, (NormalAugmentation.globalGap g Mlimit / 2) * ‖w‖ ^ 2 ≤
                inner ℝ (augmentedNormal imageCurrent Wcurrent (innerCutoff hrInner hInnerCell) w) w) ∧
              (∀ w : OutputL2 n, (NormalAugmentation.globalGap g Mlimit / 2) * ‖w‖ ^ 2 ≤
                ‖(augmentedRow imageCurrent Wcurrent (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
              let Arow := augmentedRow imageCurrent Wcurrent (innerCutoff hrInner hInnerCell)
              let Erow := CoerciveInverse.normalOperator Arow
              let Q₀ := Erow.inverse
              Erow.IsInvertible ∧ IsSelfAdjoint Q₀ ∧
              Erow ∘L Q₀ = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
              Q₀ ∘L Erow = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
              ‖Q₀‖ ≤ (NormalAugmentation.globalGap g Mlimit / 2)⁻¹ ∧
              Arow ∘L CoerciveInverse.rightInverse Arow = ContinuousLinearMap.id ℝ (OutputL2 n) ∧
              (∀ f : OutputL2 n,
                ‖CoerciveInverse.rightInverse Arow f‖ ^ 2 ≤
                  (NormalAugmentation.globalGap g Mlimit / 2)⁻¹ * ‖f‖ ^ 2 ∧
                (∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
                  (CoerciveInverse.rightInverse Arow f).snd x = 0) ∧
                (∀ᵐ x ∂volume, centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
                  physicalRow imageCurrent Wcurrent (CoerciveInverse.rightInverse Arow f).fst x = f x)) ∧
              let S := periodicSobolevScale n (Euclidean n)
              let densityProfile := fun p ↦ ∑ i, cNorm
                (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8)) p (v i)
              (∀ s w, w ∈ S.level s → Erow w ∈ S.level (s + 1) → w ∈ S.level (s + 1)) ∧
              (∀ s w, w ∈ S.level (s + 1) → Erow w ∈ S.level (s + 1) →
                S.gradeNorm (s + 1) w ≤ Cell (s + 1) *
                  (S.gradeNorm (s + 1) (Erow w) + S.gradeNorm s w +
                    (1 + densityProfile (s + 1 + (2 * (n + 1) + 14))) * ‖w‖)) ∧
              (∀ s f, f ∈ S.level s → Q₀ f ∈ S.level s ∧
                S.gradeNorm s (Q₀ f) ≤ ContinuumInverse.bootstrapConstant
                  (NormalAugmentation.globalGap g Mlimit / 2) Cell s *
                  (S.gradeNorm s f + (1 + densityProfile (s + (2 * (n + 1) + 14))) * ‖f‖)) ∧
              (v = (fun _ _ ↦ 0) →
                (∀ s w, w ∈ S.level s →
                  Arow.adjoint w ∈ augmentedInputLevel n ι s ∧
                  (augmentedInputSobolevScale n ι).gradeNorm s (Arow.adjoint w) ≤
                    Kraw s * (S.gradeNorm s w + ‖w‖)) ∧
                (∀ s f, f ∈ S.level s →
                  CoerciveInverse.rightInverse Arow f ∈ augmentedInputLevel n ι s ∧
                  S.gradeNorm s (Q₀ f) + (augmentedInputSobolevScale n ι).gradeNorm s
                      (CoerciveInverse.rightInverse Arow f) ≤
                    Cfull s * (S.gradeNorm s f + ‖f‖)) ∧
                ∀ s f, f ∈ S.level (s + 1) →
                  let raw := CoerciveInverse.rightInverse Arow f
                  ∃ hf : ∀ i, MemRawSobolev 1 (raw.fst.snd i),
                    (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
                      (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                        (angularWidth_spec (hηb i) (hr' i)).1 (raw.fst.snd i) (hf i))) ∧
                      MemPhysicalSobolev s (physicalComplexifyL2
                      (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                        (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (raw.fst.snd i) (hf i)))) ∧
                    densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s raw ≤
                      Dfull s * (S.gradeNorm (s + 1) f + ‖f‖) ∧
                    densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s raw ≤
                      Dfull s * (S.gradeNorm (s + 1) f + ‖f‖)) ∧
    
              (∀ vDensity : ι → CarrierVariable n → ℝ,
                (∀ i, ContDiff ℝ ∞ (vDensity i)) →
                (∀ i p, 1 + vDensity i p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
                (∀ i, v i = PositiveBackground.densityOnInitialLabels (vDensity i)) →
                let highSize := fun s ↦ 1 + densityProfile (s + (2 * (n + 1) + 14))
                let dCorrected := fun i ↦ CorrectedPositiveInverse.correctedCarrierData
                  (normalizedCarrierData (family i) (seed i).Q H.map (rowi i) (coli i)
                    (seed i).forward (seed i).inverse (fun _ ↦ 1) hrMeasure hMeasureCell
                    (angular i) FixedCutoffs.highFrequency σ) (vDensity i)
                (∀ i,
                  (∀ f : carrierInitialTestSpace n,
                    Wcurrent i (carrierInitialTestToLp f) =ᵐ[volume]
                      carrierTestIntegral (dCorrected i) f.val) ∧
                  (∀ w : ComplexOutputL2 n, (Wcurrent i).adjoint w =ᵐ[carrierMeasure n]
                    carrierAdjointIntegral (dCorrected i) w)) ∧
                (∀ s w, w ∈ S.level s →
                  Arow.adjoint w ∈ augmentedInputLevel n ι s ∧
                  (augmentedInputSobolevScale n ι).gradeNorm s (Arow.adjoint w) ≤
                    Kpositive s * (S.gradeNorm s w + highSize s * ‖w‖)) ∧
                (∀ s f, f ∈ S.level s →
                  CoerciveInverse.rightInverse Arow f ∈ augmentedInputLevel n ι s ∧
                  S.gradeNorm s (Q₀ f) + (augmentedInputSobolevScale n ι).gradeNorm s
                      (CoerciveInverse.rightInverse Arow f) ≤
                    Cpositive s * (S.gradeNorm s f + highSize s * ‖f‖)) ∧
                ∀ s f, f ∈ S.level (s + 1) →
                  let raw := CoerciveInverse.rightInverse Arow f
                  ∃ hf : ∀ i, MemRawSobolev 1 (raw.fst.snd i),
                    (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
                      (densityUncut (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                        (angularWidth_spec (hηb i) (hr' i)).1 (raw.fst.snd i) (hf i))) ∧
                      MemPhysicalSobolev s (physicalComplexifyL2
                      (density (z i) (NormedSpace.normalize (ηb i)) (ha' i)
                        (angularWidth_spec (hηb i) (hr' i)).1 (χinitial i) (raw.fst.snd i) (hf i)))) ∧
                    densityUncutFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) s raw ≤
                      Dpositive s * (S.gradeNorm (s + 1) f + highSize (s + 1) * ‖f‖) ∧
                    densityFamilySize z (fun i ↦ NormedSpace.normalize (ηb i)) ha'
                      (fun i ↦ (angularWidth_spec (hηb i) (hr' i)).1) χinitial s raw ≤
                      Dpositive s * (S.gradeNorm (s + 1) f + highSize (s + 1) * ‖f‖))) ∧
        ∃ Ccompare Bsource Mzero : ι → ℝ,
        (∀ i, 0 < Ccompare i) ∧ (∀ i, 0 < Bsource i) ∧ (∀ i, 0 ≤ Mzero i) ∧
        ∀ targetGap > (0 : ℝ),
        let tol := targetGap / (4 * ((Fintype.card ι : ℝ) + 1))
        ∃ cap > (0 : ℝ), ∃ hcapSource : cap ≤ densityCap, cap ≤ 1 ∧
        ∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap),
        ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
          (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4))) →
          (∀ i q, q ∈ ball ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 4) → 0 < 1 + v i q) →
          (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8) →
            1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          (∀ i, cNorm (closedBall ((0 : Euclidean (n - 1)), zScalar i) (Lscalar i / 8)) (μ + 14) (v i) ≤ 1) →
        let cσ := current σ ⟨hσ.1, hσ.2.trans hcapSource⟩
        let e : ι → CarrierData n (embeddingDimension n) := fun i ↦
          data (family i) (cσ i).Q (sourceDilation H.map σ) (rowi i) (coli i) (cσ i).forward (cσ i).inverse
            (fun q ↦ positiveDensityAmplitude σ (v i q)) (ha' i) (hcell i) (angular i)
            FixedCutoffs.highFrequency
        let pair := fun (t : Fin 2) i ↦ b i (![σ, 0] t) (v i)
        (∀ i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair 0 i ξ z j k - pair 1 i ξ z j k) μ tol) ∧
        ∃ hb : ∀ t i, ContDiff ℝ ∞ (Function.uncurry (pair t i)),
        ∃ hs : ∀ t i ξ j k, SupportedInCenteredBox (4 * a' i) (fun z ↦ pair t i ξ z j k),
        ∃ hB : ∀ t i j k, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t i ξ z j k) μ (Bsource i),
        let Aop := fun t i ↦ vectorTwoPositionL2Operator (by omega) (4 * a' i) (pair t i) (hb t i) (hs t i)
          (Bsource i) (hB t i)
        let Nop := fun t i ↦ realOutputCompression (transferOperator (Aop t i))
        ∃ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ Wop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i f, Wop i (carrierInitialTestToLp f) =ᵐ[volume]
              carrierTestIntegral (e i) f.val) → Wop = Vop) ∧
          (∀ i, ‖Vop i‖ ≤ Real.sqrt ((n : ℝ) ^ (2 : ℕ) * (fixedBoxAmplitudeConstant n (4 * a' i) * Ccompare i))) ∧
          (∀ i,
            (∀ f : carrierInitialTestSpace n, Vop i (carrierInitialTestToLp f) =ᵐ[volume]
              carrierTestIntegral (e i) f.val) ∧
            (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
              (Vop i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
            carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint = Nop 0 i ∧
            ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint - Nop 1 i‖ ≤ tol) ∧
          (∑ i, ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint - Nop 1 i‖) ≤ targetGap / 4 ∧
          (∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
            ‖∑ i, (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i)) ∘L
              (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i))).adjoint -
              cutoffMultiplier χ ∘L Nop 1 i ∘L cutoffMultiplier χ)‖ ≤ targetGap / 4) ∧
          ∃ Vzero : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
            (∀ i, ‖Vzero i‖ ≤ Mzero i ∧ ‖(Vzero i).adjoint‖ ≤ Mzero i) ∧
            (∀ i,
              (∀ f : carrierInitialTestSpace n,
                Vzero i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) ∧
              (∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral (eZero i (v i)) f) 2 (carrierMeasure n) ∧
                (Vzero i).adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral (eZero i (v i)) f) ∧
              (∀ Wzero : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                (∀ f : carrierInitialTestSpace n,
                  Wzero (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral (eZero i (v i)) f.val) →
                  Wzero = Vzero i) ∧
              carrierChannel (Vzero i) ∘L (carrierChannel (Vzero i)).adjoint = Nop 1 i) ∧
            (∑ i, ‖carrierChannel (Vop i) ∘L (carrierChannel (Vop i)).adjoint -
              carrierChannel (Vzero i) ∘L (carrierChannel (Vzero i)).adjoint‖) ≤ targetGap / 4 ∧
            ∀ χ : C(Torus n, ℝ), ‖χ‖ ≤ 1 →
              ‖∑ i, (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i)) ∘L
                (carrierChannel (CommonMeasurement.restrictCarrier χ (Vop i))).adjoint -
                carrierChannel (CommonMeasurement.restrictCarrier χ (Vzero i)) ∘L
                (carrierChannel (CommonMeasurement.restrictCarrier χ (Vzero i))).adjoint)‖ ≤ targetGap / 4) ∧
        let J := (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) × centers i
        ∀ δgeometry : J → ℝ, (∀ i, 0 < δgeometry i) →
        ∃ sourceCap > (0 : ℝ), sourceCap ≤ 1 ∧
        ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) sourceCap → (i : J) →
          PositiveReference.FlowConstruction.Chart (T i.1) (Ωc i.1 i.2)
            (closedBall ((0 : Euclidean n), i.2.1.1) (ρc i.1 i.2))
            ((0 : Euclidean (n - 1)), i.2.1.1) (Rc i.1 i.2) (Bc i.1 i.2) (τc i.1 i.2)
            (row i.1 i.2) (col i.1 i.2) (sourceDilation H.map σ),
        ∀ σ hσ i,
          ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
              ℝ × (Euclidean (n - 1) × Euclidean 3),
          ODE.IsSmoothFlowOn
            (NullTransport.ActualFlow.liftedDirection (T i.1) (current σ hσ i).Q
              (row i.1 i.2) (col i.1 i.2))
            (0, ((0 : Euclidean (n - 1)), i.2.1.1)) (Rc i.1 i.2) (Rc i.1 i.2 / 2)
            (existenceTime (Rc i.1 i.2)
              (NullTransport.ActualFlow.liftedLowBound (T i.1) (Bc i.1 i.2))) Ψ ∧
          (current σ hσ i).forward = forwardFromLift Ψ ∧
          (current σ hσ i).inverse = footpointFromLift Ψ ∧
          IsImmersionOn (sourceDilation H.map σ) (ball 0 R) ∧
          HasFullNormalRankOn (sourceDilation H.map σ) (ball 0 R) ∧
          cNorm (closedBall (0 : Euclidean n) (T i.1).data.localReference.stateRadius) 6
            ((current σ hσ i).Q.1 - fun _ ↦ cubeStress n) < δgeometry i ∧
          EqOn (current σ hσ i).forward (sourceTransportFlow (seed i.1 i.2).forward σ)
            (Ioo (-τc i.1 i.2) (τc i.1 i.2) ×ˢ
              ball ((0 : Euclidean (n - 1)), i.2.1.1) (Rc i.1 i.2 / 8)) ∧
          EqOn (current σ hσ i).inverse (sourceTransportFlow (seed i.1 i.2).inverse σ)
            (current σ hσ i).D ∧
          EqOn ((current σ hσ i).scalar (fun _ ↦ σ))
            (sourceAmplitude ((seed i.1 i.2).scalar (fun _ ↦ 1)) σ)
            ((coordinates (adaptedCoordinates (T i.1).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
          EqOn (fun w ↦ (current σ hσ i).scalar (fun _ ↦ σ) w •
              carrierNullvector (T i.1) (current σ hσ i).Q (col i.1 i.2) w)
            (sourceAmplitude (fun w ↦ (seed i.1 i.2).scalar (fun _ ↦ 1) w •
              carrierNullvector (T i.1) (seed i.1 i.2).Q (col i.1 i.2) w) σ)
            ((coordinates (adaptedCoordinates (T i.1).data.adapted)) ⁻¹' (current σ hσ i).D) ∧
          ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
            EqOn ((current σ hσ i).scalar (fun q ↦ σ * weight q))
              (fun w ↦ sourceAmplitude ((seed i.1 i.2).scalar (fun _ ↦ 1)) σ w *
                weight ((current σ hσ i).inverse
                  (coordinates (adaptedCoordinates (T i.1).data.adapted) w)))
              ((coordinates (adaptedCoordinates (T i.1).data.adapted)) ⁻¹' (current σ hσ i).D)) ∧
      (∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      let ρ := θ * σ
      0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.map = sourceDilation H.map σ ∧
        G.domain.coreRadius = εcommon / 4 ∧ G.domain.chartRadius = εcommon / 2 ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean n) b) j
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
      (∃ δ C₀ κ : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧
        (∀ (V : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
          IsOpen V → closedBall 0 R ⊆ V → ContDiffOn ℝ ∞ F V →
          cNorm (closedBall 0 R) 8 (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
          (∀ x ∈ ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
          (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
          ∀ i, cNorm (closedBall 0 b) 6
            (fun x ↦ projectedStress F x i - cubeStress n i) < εframe) ∧
        IsImmersionOn G.map (ball 0 R) ∧ HasFullNormalRankOn G.map (ball 0 R) ∧
        cNorm (closedBall 0 b) 4 G.map ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ G.map x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace G.map x,
          κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖) ) ∧
      (∀ rStar r₀ kMin : ℕ, 14 ≤ rStar → 14 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∀ Mᵣ m₀ : ℝ, 0 ≤ Mᵣ → 0 < m₀ →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ κ > 0,
    ∃ c : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ, ∃ Amap : ℕ → ℝ, ∃ E : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℕ → ℝ,
    ∃ A H B : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℕ → ℝ,
      (∀ i, 0 < c i) ∧ (∀ m, 0 ≤ Amap m) ∧ (∀ i m, 0 < E i m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      let K := closedBall (0 : Euclidean n) b
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm K 14 F ≤ cNorm K 14 G.map + 1 ∧
        (∀ x ∈ ball 0 R, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile K F rStar (currentCoefficientScale R₀ stage) Amap ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∀ i,
        let T := T i
        let P := D.patches i.1 i.2
        let Ωc := Ωc i
        let ρc := ρc i
        let Bc := Bc i
        let gc := gc i
        let centers := centers i
        let row := row i
        let col := col i
        let ρ := ρlead i
        let R := L i
        let τ := τ i
        let Rc := Rc i
        let τc := τc i
        let Mc := Mc i
        let rcomp := rcomp i
        let δcomp := δcomp i
        let σ := σcover i
        let c := c i
        let E := E i
        let A := A i
        let H := H i
        let B := B i
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
        ∀ j : centers,
        let z₀ := j.1.1
        let Ωc := Ωc j
        let ρc := ρc j
        let Bc := Bc j
        let gc := gc j
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        cNorm (closedBall a ρ) 1 (transportDirection T Q row col) ≤ Bfull i j ∧
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          (ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ωc ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ωc ∧
            cNorm (closedBall ((0 : Euclidean n), z₀) ρc) 1
              (carrierTransportDirection T Q row col) ≤ Bc ∧
            (∀ w ∈ Ωc, ∀ i, (Q.1 w.1 i).IsSymm) ∧
            (∀ w ∈ Ωc,
              carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
              carrierConullvector T Q row w ᵥ*
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
              gc ≤ |carrierAdaptedDenominator T Q row col w| ∧
              carrierAdaptedDenominator T Q row col w ≠ 0 ∧
              |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ gc⁻¹) ∧
            Dc = (fun q ↦ (q.1, φ q)) ''
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            Dc ⊆ Cc.symm ⁻¹' Ωc ∧ Cc ⁻¹' Dc ⊆ Ωc ∧
            Cc ⁻¹' Dc ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              parameterInterior (3 * P.radius / 2) ∧
            ContDiffOn ℝ ∞ φ
              (Ioo (-τc) τc ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8)) ∧
            ContDiffOn ℝ ∞ y Dc ∧
            (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (Rc / 8),
              ∀ t ∈ Ioo (-τc) τc, (φ (t, p)).2 = p.2) ∧
            (∀ q ∈ Dc, (y q).2 = q.2.2) ∧
            ContDiffOn ℝ ∞ y (Ioo (-(2 * τc)) (2 * τc) ×ˢ
              ball ((0 : Euclidean (n - 1)), z₀) (Rc / 4))) ∧
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          LeadingWave.FullModulation.phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m₀ ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r) ∧
            cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
              |B j| * ((1 + Amap (j + 13)) *
                currentCoefficientScale R₀ stage ^ (j - r₀) +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (LeadingWave.FullModulation.phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (LeadingWave.FullModulation.phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ LeadingWave.FullModulation.phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) ∧
            cNorm J₀ j (fun w ↦ LeadingWave.FullModulation.phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * ((1 + Amap (j + 14)) *
                currentCoefficientScale R₀ stage ^ (j - r₀) +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) ∧
            cNorm J₀ j (fun w ↦ LeadingWave.FullModulation.phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              (E j * (1 + Amap (j + 14) +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) *
                  currentCoefficientScale R₀ stage ^ (j - r₀)) ∧
      (∀ rStar r₀ kMin : ℕ, 8 ≤ rStar → 6 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Bquotient Eext : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧ (∀ m, 0 ≤ Bquotient m) ∧ (∀ m, 0 ≤ Eext m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 b) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 b) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 b) ∧
        tsupport (extendedReducedCoefficients qext (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (b + qext.width / 2) ∧
        HasDerivativeProfile univ (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) r₀
          (currentCoefficientScale R₀ j) Eext ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∀ i,
          let T := T i
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
          let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
          BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (fullParameterSet (z i) (s i) (2 * e i))
            (dataBox (z i) ηb (qrad i)) (dataSet (z i) ηb (2 * qrad i))
            (dataBox (z i) ηb (2 * qrad i)) (VF i) (LF i) (bF i) (cF i)
            (FrozenIncidence.referenceEquiv T ((hD.2.2.2.2.1 i.1 i.2).1) (hz i) (hinc i) (hd i)) ∧
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet (z i) (s i) (2 * e i))
            (closedBall ηb (qrad i)) (ball ηb (2 * qrad i)) (closedBall ηb (2 * qrad i))
            (VT i) (LT i) (bT i) (cT i) (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (HamiltonPhase.phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ∀ m, currentQuotientCoefficientNorm T Q (z i) ηb
              (ρF i) (ρT i) (qrad i) (s i) (e i) (VF i) (VT i) m ≤
            Bquotient m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
      (∀ rStar r₀ kMin : ℕ, 12 ≤ rStar → 6 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Bquotient Btransport Egeom Eext Bextended : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧ (∀ m, 0 ≤ Bquotient m) ∧ (∀ m, 0 ≤ Btransport m) ∧
      (∀ m, 0 ≤ Egeom m) ∧ (∀ m, 0 ≤ Eext m) ∧ (∀ m, 0 ≤ Bextended m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 b) 4 F ≤ C₀ ∧
        cNorm (closedBall 0 b) 12 F ≤ cNorm (closedBall 0 b) 12 G.map + 1 ∧
        cNorm (closedBall 0 b) 6 (projectedStress F - fun _ ↦ cubeStress n) < εframe ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 b) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 b) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        (∀ m, extendedGeometricCoefficientNorm qext m F ≤
          Egeom m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 b) ∧
        tsupport (extendedReducedCoefficients qext (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (b + qext.width / 2) ∧
        HasDerivativeProfile univ (extendedReducedCoefficients qext (fun _ _ ↦ 0) F) r₀
          (currentCoefficientScale R₀ j) Eext ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∀ i,
          let T := T i
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
          let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
          BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (fullParameterSet (z i) (sext i) (2 * eext i))
            (dataBox (z i) ηb (qextRad i)) (dataSet (z i) ηb (2 * qextRad i))
            (dataBox (z i) ηb (2 * qextRad i)) (VFext i) (LFext i) (bFext i) (cFext i)
            (FrozenIncidence.referenceEquiv T ((hD.2.2.2.2.1 i.1 i.2).1) (hz i) (hinc i) (hd i)) ∧
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet (z i) (sext i) (2 * eext i))
            (closedBall ηb (qextRad i)) (ball ηb (2 * qextRad i)) (closedBall ηb (2 * qextRad i))
            (VText i) (LText i) (bText i) (cText i) (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (HamiltonPhase.phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ContDiff ℝ ∞ (extendedHamiltonPhase T Q) ∧
          EqOn (extendedHamiltonPhase T Q) (HamiltonPhase.phase (T.currentChart Q).coordinates)
            (closedBall (hamiltonExtensionCenter T) (hamiltonExtensionRadius T)) ∧
          tsupport (extendedHamiltonPhase T Q) ⊆ hamiltonExtensionSupport T ∧
          HasDerivativeProfile univ (extendedHamiltonPhase T Q) r₀
            (currentCoefficientScale R₀ j) Bextended ∧
          (∀ f ∈ ({fullForwardCoefficient T Q,
              fullForwardEpsilonCoefficient T Q} : Set (FullQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ ψF i x • f x) ∧
            EqOn (fun x ↦ ψF i x • f x) f
              (fullParameterBox (z i) (sext i / 2) (eext i) ×ˢ dataBox (z i) ηb (2 * qextRad i)) ∧
            tsupport (fun x ↦ ψF i x • f x) ⊆ tsupport (ψF i)) ∧
          (∀ f ∈ ({transverseForwardCoefficient T Q,
              transverseForwardEpsilonCoefficient T Q} : Set (TransverseQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ ψT i x • f x) ∧
            EqOn (fun x ↦ ψT i x • f x) f
              (transversePrimitiveBox (z i) (sext i / 2) (eext i) ×ˢ closedBall ηb (2 * qextRad i)) ∧
            tsupport (fun x ↦ ψT i x • f x) ⊆ tsupport (ψT i)) ∧
          (∀ f ∈ ({fullInverseCoefficient T Q (z i) ηb (qextRad i),
              fullInverseEpsilonCoefficient T Q (z i) ηb (qextRad i)} : Set (FullQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ χF i x • f x) ∧
            EqOn (fun x ↦ χF i x • f x) f
              (fullParameterBox (z i) (sext i / 4) (eext i / 2) ×ˢ LFext i) ∧
            tsupport (fun x ↦ χF i x • f x) ⊆ tsupport (χF i)) ∧
          (∀ f ∈ ({transverseInverseCoefficient T Q ηb (qextRad i),
              transverseInverseEpsilonCoefficient T Q ηb (qextRad i)} : Set (TransverseQuotientInput n → _)),
            ContDiff ℝ ∞ (fun x ↦ χT i x • f x) ∧
            EqOn (fun x ↦ χT i x • f x) f
              (transversePrimitiveBox (z i) (sext i / 4) (eext i / 2) ×ˢ LText i) ∧
            tsupport (fun x ↦ χT i x • f x) ⊆ tsupport (χT i)) ∧
          (∀ m, extendedQuotientCoefficientNorm T Q (z i) ηb (qextRad i)
              (ψF i) (ψT i) (χF i) (χT i) m ≤
            Dq i m * currentQuotientCoefficientNorm T Q (z i) ηb
              (ρFext i) (ρText i) (qextRad i) (sext i) (eext i) (VFext i) (VText i) m) ∧
          (∀ m, extendedQuotientCoefficientNorm T Q (z i) ηb (qextRad i)
              (ψF i) (ψT i) (χF i) (χT i) m ≤
            Bquotient m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
          ∀ q : transportCenters i,
            ContDiffOn ℝ ∞ (carrierNullvector T Q (transportCol i q)) (Ωtransport i q) ∧
            ContDiffOn ℝ ∞ (carrierConullvector T Q (transportRow i q)) (Ωtransport i q) ∧
            ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q)) (Ωtransport i q) ∧
            ContDiffOn ℝ ∞ (fun w ↦ (carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q) w)⁻¹)
              (Ωtransport i q) ∧
            ContDiffOn ℝ ∞ (carrierTransportDirection T Q (transportRow i q) (transportCol i q)) (Ωtransport i q) ∧
            ContDiffOn ℝ ∞ (carrierTransportPotential T Q F (transportRow i q) (transportCol i q)) (Ωtransport i q) ∧
            (∀ w ∈ Ωtransport i q,
              carrierNullvector T Q (transportCol i q) w ≠ 0 ∧ carrierConullvector T Q (transportRow i q) w ≠ 0 ∧
              gtransport i ≤ |carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q) w| ∧
              |(carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q) w)⁻¹| ≤ (gtransport i)⁻¹) ∧
            cNorm (closedBall ((0 : Euclidean n), q.1.1) (ρtransport i q)) 1
              (carrierTransportDirection T Q (transportRow i q) (transportCol i q)) ≤ Ltransport i q ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (carrierNullvector T Q (transportCol i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (carrierConullvector T Q (transportRow i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (fun w ↦ (carrierAdaptedDenominator T Q (transportRow i q) (transportCol i q) w)⁻¹) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (carrierTransportDirection T Q (transportRow i q) (transportCol i q)) ∧
            TransportExtensionProperties ((0 : Euclidean n), q.1.1) (hρtransport i q)
              (carrierTransportPotential T Q F (transportRow i q) (transportCol i q)) ∧
            ∀ m,
              extendedTransportCoefficientNorm T Q F (transportRow i q) (transportCol i q)
                  ((0 : Euclidean n), q.1.1) (hρtransport i q) m ≤
                Dt i m * currentTransportCoefficientNorm T Q F (transportRow i q) (transportCol i q)
                  (closedBall ((0 : Euclidean n), q.1.1) (ρtransport i q)) m ∧
              extendedTransportCoefficientNorm T Q F (transportRow i q) (transportCol i q)
                  ((0 : Euclidean n), q.1.1) (hρtransport i q) m ≤
                Btransport m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
      ∀ (gtarget : MetricField n) (Vtarget : Set (Euclidean n)),
        IsOpen Vtarget → (0 : Euclidean n) ∈ Vtarget →
        IsRiemannianMetricOn gtarget Vtarget →
        ∀ kMin : ℕ,
          displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin →
          ∃ M : MetricTensor n, IsUnit M ∧ coordinatePullback gtarget M 0 = 1 ∧
        ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
          ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
            W ⊆ G.domain.core n ∧
            ∃ B L A C : ℕ → ℝ, (∀ r, 0 < B r) ∧
              (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ A r) ∧ (∀ k, 0 ≤ C k) ∧
              (∀ s ∈ Icc (0 : ℝ) s₀,
                (∀ x ∈ G.domain.closureChart n, coordinateMap M ((s * ρ) • x) ∈ Vtarget) ∧
                IsRiemannianMetricOn (scaledMetric (coordinatePullback gtarget M) (s * ρ)) (G.domain.closureChart n) ∧
                ContinuousOn (scaledMetric (coordinatePullback gtarget M) (s * ρ)) (G.domain.core n) ∧
                (∀ r, cNorm (G.domain.closureChart n) r
                  (scaledMetric (coordinatePullback gtarget M) (s * ρ) - inducedMetric G.map) ≤ B r * s) ∧
                cNorm (G.domain.core n) 0
                  (inducedMetric G.map - scaledMetric (coordinatePullback gtarget M) (s * ρ)) ≤ B 0 * s) ∧
              (∀ cap : ℝ, 0 < cap → cap ≤ s₀ → ∀ η : ℝ, 0 < η →
                ∀ (orders : Finset ℕ) (ε : ℕ → ℝ), (∀ r ∈ orders, 0 < ε r) →
                  ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
                    cNorm (G.domain.core n) 0
                      (inducedMetric G.map - scaledMetric (coordinatePullback gtarget M) (s * ρ)) ≤ η ∧
                    ∀ r ∈ orders, cNorm (G.domain.closureChart n) r
                      (scaledMetric (coordinatePullback gtarget M) (s * ρ) - inducedMetric G.map) < ε r) ∧
              (∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
                ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
                  (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
                let R := iterationScale R₀ growthExponent j
                let δ := R ^ (-(k : ℝ))
                let gs := scaledMetric (coordinatePullback gtarget M) (s * ρ)
                let e := historyDefect gs G.map u
                cNorm (G.domain.core n) 0 e ≤ δ ^ 2 →
                let eR := smoothedHistoryDefect G.domain R gs G.map u
                IsSmoothPeriodic eR ∧ HasFourierSupport (2 * R) eR ∧
                ((∀ x ∈ G.domain.core n, (gs x).IsSymm) → ∀ z, (eR z).IsSymm) ∧
                (∀ r (K : Set (Euclidean n)),
                  cNorm K r (periodicLift eR) + periodicSobolevNorm (r : ℝ) eR ≤
                    L r * δ ^ 2 * R ^ r) ∧
                (∀ r (K : Set (Euclidean n)),
                  cNorm K r (periodicLift
                      (normalizedHistorySource G.domain R δ gs G.map u)) +
                    periodicSobolevNorm (r : ℝ)
                      (normalizedHistorySource G.domain R δ gs G.map u) ≤
                    A r * R ^ ((r : ℝ) - 2 * forcingExponent n)) ∧
                cNorm (G.domain.core n) 0 (e - periodicLift eR) ≤
                  C k * δ * R ^ (-2 * (k : ℝ)) ∧
                (∀ x ∈ G.domain.core n, ‖periodicLift eR x - e x‖ ≤
                  C k * δ * R ^ (-2 * (k : ℝ))))) ∧
          ∃ hQ : ContDiffOn ℝ ∞ (projectedStress H.map) (ball (0 : Euclidean n) R),
          ∃ hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            (projectedStress H.map - fun _ ↦ cubeStress n) < (T a).family.threshold,
          ∃ centers : (a : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → Finset (parameterCube (D.patches a.1 a.2).radius),
          ∃ radius : (a : ((j : Fin D.chartCount) × Fin (D.patchCount j))) → centers a → ℝ,
            (∀ a j, 0 < radius a j) ∧
            (∀ a, parameterCube (D.patches a.1 a.2).radius ⊆ ⋃ j : centers a,
              ball j.1.1 (radius a j / 4)) ∧
            ∃ ε : ℝ, 0 < ε ∧ ball (0 : Euclidean n) (2 * ε) ⊆ H.domain.chart n ∧
            (∀ a, 2 * ε < (T a).physicalRadius) ∧
            let I := (a : ((j : Fin D.chartCount) × Fin (D.patchCount j))) × centers a
            let Q := fun a ↦ (⟨projectedStress H.map, hQ, hlow a⟩ :
              {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
                cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                  (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
            (∀ a,
              (∀ z ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
                ⟪(normalizedHomogeneousSymbol isOpen_ball (Q a).1 (Q a).2.1).hp z,
                  (T a).data.adapted.normal⟫_ℝ ≠ 0) ∧
              ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n //
                    ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
                    cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
                      (Q - fun _ ↦ cubeStress n) < (T a).family.threshold},
                  Qσ.1 = projectedStress (sourceDilation H.map σ) ∧
                  EqOn ((T a).currentChart Qσ).coordinates
                    (sourceCoordinates ((T a).currentChart (Q a)).coordinates σ) (T a).target ∧
                  EqOn (HamiltonPhase.phase ((T a).currentChart Qσ).coordinates)
                    (sourcePhase (HamiltonPhase.phase ((T a).currentChart (Q a)).coordinates) σ) (T a).target ∧
                  (∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (HamiltonPhase.phase ((T a).currentChart Qσ).coordinates))
                    (iteratedFDeriv ℝ m
                      (sourcePhase (HamiltonPhase.phase ((T a).currentChart (Q a)).coordinates) σ)) (T a).target) ∧
                  (let S := fun p : Euclidean n × Euclidean (n - 1) ↦
                      HamiltonPhase.phase ((T a).currentChart (Q a)).coordinates (p.1, (0, p.2))
                   let ζ := fun z ↦ (T a).reference.spatialPatch (CanonicalCarrier.parameter z)
                   let B := ball (0 : Euclidean n) (T a).physicalRadius ×ˢ
                     (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * (D.patches a.1 a.2).radius))
                   EqOn (CanonicalCarrier.transportPosition (T a) Qσ)
                     (sourceTransportPosition S ζ σ) B ∧
                   ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (CanonicalCarrier.transportPosition (T a) Qσ))
                     (iteratedFDeriv ℝ m (sourceTransportPosition S ζ σ)) B) ∧
                  ∀ x ∈ ball (0 : Euclidean n) (T a).physicalRadius,
                    ∀ z ∈ parameterCube (2 * (D.patches a.1 a.2).radius),
                      (T a).carrier Qσ x z =
                        sourcePhase (fun p ↦ (T a).carrier (Q a) p.1 p.2) σ (x, z) ∧
                      (T a).carrierGradient Qσ x z = (T a).carrierGradient (Q a) (σ • x) z ∧
                      ∀ col, carrierNullvector (T a) Qσ col (x, z) =
                        carrierNullvector (T a) (Q a) col (σ • x, z) ) ∧
            let S := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ (T j.1).carrier (Q j.1) p.1 p.2
            let ξ := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
              (T j.1).carrierGradient (Q j.1) p.1 p.2
            let V := fun j : I ↦ ball j.2.1.1 (radius j.1 j.2 / 2)
            let Kc := fun j : I ↦ closedBall j.2.1.1 (radius j.1 j.2 / 4)
            ∃ b : I → Euclidean n × Euclidean 3 → Euclidean n,
            (∀ j : I,
            let T := T j.1
            let P := D.patches j.1.1 j.1.2
            let Q := Q j.1
            let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
            let z := j.2.1.1
            let r := radius j.1 j.2
            ∃ row col : Fin n, ∃ τ Rflow : ℝ, 0 < τ ∧ 0 < Rflow ∧
            ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
            ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
              b j = (fun w ↦ carrierScalarAmplitude T Q H.map row col Φ Y (fun _ ↦ 1) w •
                carrierNullvector T Q col w) ∧
              (ball (0 : Euclidean n) (2 * ε) ×ˢ ball z (r / 2) ⊆ C ⁻¹' D) ∧
              IsOpen D ∧
              Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (Rflow / 32) ⊆ D ∧
              C ⁻¹' D ⊆ (ball (0 : Euclidean n) R) ×ˢ parameterInterior (3 * P.radius / 2) ∧
              D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (Rflow / 4) ∧
              ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8)) ∧
              ContDiffOn ℝ ∞ Y D ∧
              MapsTo (fun q ↦ (q.1, Φ q))
                (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8)) D ∧
              MapsTo (fun q ↦ (q.1, Y q)) D
                (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8)) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8), Φ (0, p) = p) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8), ∀ t ∈ Ioo (-τ) τ,
                Y (t, Φ (t, p)) = p) ∧
              (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8), ∀ t ∈ Ioo (-τ) τ,
                (Φ (t, p)).2 = p.2) ∧
              (∀ q ∈ D, (Y q).2 = q.2.2) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8), ∀ t ∈ Ioo (-τ) τ,
                HasDerivAt (fun s ↦ Φ (s, p))
                  ((adaptedCoordinates T.data.adapted
                    (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
              let α := carrierScalarAmplitude T Q H.map row col Φ Y (fun _ ↦ 1)
              ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
              (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8),
                α (T.data.adapted.embedding p.1, p.2) = 1) ∧
              (∀ w ∈ C ⁻¹' D, 0 < α w ∧ α w • carrierNullvector T Q col w ≠ 0) ∧
              (∀ w ∈ C ⁻¹' D,
                fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
                  carrierTransportPotential T Q H.map row col w * α w = 0) ∧
              (∀ w ∈ C ⁻¹' D,
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
              (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator H.map Q.1
                (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
              ContDiffOn ℝ ∞ (carrierNullvector T Q col) (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) (C ⁻¹' D) ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q H.map row col) (C ⁻¹' D) ∧
              (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0) ∧
              (∀ z₀ ∈ V j, ∃ Rflow' τ' : ℝ, 0 < Rflow' ∧ 0 < τ' ∧
                let I' := Ioo (-τ') τ'
                let L' := ball ((0 : Euclidean (n - 1)), z₀) (Rflow' / 8)
                let W' := I' ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (Rflow' / 32)
                ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
                      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation H.map σ) ∧
                    ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      IsOpen Dσ ∧ W' ⊆ Dσ ∧ C ⁻¹' Dσ ⊆ C ⁻¹' D ∧
                      ContDiffOn ℝ ∞ Φσ (I' ×ˢ L') ∧ ContDiffOn ℝ ∞ Yσ Dσ ∧
                      MapsTo (fun q ↦ (q.1, Φσ q)) (I' ×ˢ L') Dσ ∧
                      MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (I' ×ˢ L') ∧
                      (∀ p ∈ L', Φσ (0, p) = p) ∧
                      (∀ p ∈ L', ∀ t ∈ I', Yσ (t, Φσ (t, p)) = p) ∧
                      (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
                      (∀ p ∈ L', ∀ t ∈ I', HasDerivAt (fun s ↦ Φσ (s, p))
                        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
                          (C.symm (t, Φσ (t, p))))).2, 0) t) ∧
                      EqOn (carrierScalarAmplitude T Qσ (sourceDilation H.map σ) row col Φσ Yσ (fun _ ↦ σ))
                        (sourceAmplitude α σ) (C ⁻¹' Dσ) ∧
                      EqOn (fun w ↦ carrierScalarAmplitude T Qσ (sourceDilation H.map σ)
                        row col Φσ Yσ (fun _ ↦ σ) w • carrierNullvector T Qσ col w)
                        (sourceAmplitude (b j) σ) (C ⁻¹' Dσ)) ∧
              (∃ δ > (0 : ℝ), ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∀ x ∈ ball (0 : Euclidean n) δ, ∀ z' ∈ Kc j,
                  ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
                      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                        (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                    Qσ.1 = projectedStress (sourceDilation H.map σ) ∧
                    ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
                      carrierScalarAmplitude T Qσ (sourceDilation H.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') =
                        sourceAmplitude α σ (x, z') ∧
                      carrierScalarAmplitude T Qσ (sourceDilation H.map σ) row col Φσ Yσ (fun _ ↦ σ) (x, z') •
                        carrierNullvector T Qσ col (x, z') = sourceAmplitude (b j) σ (x, z')) ∧
              ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
                ∃ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball (0 : Euclidean n) R) ∧
                    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                      (Q - fun _ ↦ cubeStress n) < T.family.threshold},
                  Qσ.1 = projectedStress (sourceDilation H.map σ) ∧
                  (∀ u z', (σ • u, z') ∈ ball ((0 : Euclidean (n - 1)), z) (Rflow / 8) →
                    sourceAmplitude α σ (T.data.adapted.embedding u, z') = σ) ∧
                  ∀ x ∈ ball (0 : Euclidean n) (2 * ε), ∀ z' ∈ V j,
                    sourceAmplitude (b j) σ (x, z') =
                      sourceAmplitude α σ (x, z') • carrierNullvector T Qσ col (x, z') ∧
                    0 < sourceAmplitude α σ (x, z') ∧
                    sourceAmplitude (b j) σ (x, z') ≠ 0 ∧
                    reducedSymbol (Qσ.1 x) (T.carrierGradient Qσ x z') *ᵥ
                      (fun k ↦ sourceAmplitude (b j) σ (x, z') k) = 0 ∧
                    carrierConullvector T Qσ row (x, z') ⬝ᵥ
                      reducedOperator (sourceDilation H.map σ) Qσ.1
                        (fun y ↦ sourceAmplitude (b j) σ (y, z')) x = 0) ∧
            ∀ (w : I → Euclidean 3 → ℝ),
              (∀ j, ContDiffOn ℝ ∞ (w j) (V j)) → (∀ j z, 0 ≤ w j z) →
              (∀ j z, z ∉ Kc j → w j z = 0) →
              ∀ (D : Set (Euclidean n)), IsCompact D →
              let μ := fun _ : I ↦ (volume : Measure (Euclidean 3))
              let ν := fun j p ↦ LeadingWave.principalNormal
                (AmbientResponse.canonicalNormalCompletion H.map p.1) (ξ j p) (b j p)
              let J := fun j q ↦ (normalizedPullback (b j) q,
                normalizedPullback (ξ j) q, normalizedPullback (ν j) q)
              ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
                (∀ j, ContDiffOn ℝ ∞ (J j) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j) ∧
                  ContDiffOn ℝ ∞ (sourcePhaseExtension (S j))
                    (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j)) ∧
                (∃ c > 0, ∀ j, ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ x ∈ D, ∀ z ∈ Kc j,
                  c ≤ ‖normalizedPullback (ν j) (ρ, (x, z))‖) ∧
                (carrierMean μ w ν ξ 0).PosSemidef ∧
                (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ B,
                  sourcePrincipalMean H.map μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x ∧
                  PositiveBackground.referenceMeanResidual (sourceDilation H.map ρ)
                    (carrierMean μ w ν ξ 0) (sourcePrincipalMean H.map μ w S b ρ) x =
                    sourcePrincipalMean H.map μ w S b ρ x - carrierMean μ w ν ξ 0 ∧
                  ∀ j z, z ∈ V j → sourcePhase (S j) ρ (x, z) =
                    sourcePhaseExtension (S j) (ρ, (x, z))) ∧
                ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
                  cNorm D s (fun x ↦ sourcePrincipalMean H.map μ w S b ρ x -
                    carrierMean μ w ν ξ 0) ≤ C * ρ ∧
                  ∀ j x, x ∈ D → ∀ z ∈ Kc j,
                    ‖iteratedFDeriv ℝ s (J j) (ρ, (x, z))‖ ≤ C := by
  classical
  have initialized := exists_common_initializer_with_normalized_charts_and_density_products hn
  choose G₀ hG₀ b R hb hbR hR D c C hD kCenter hkCenter hkDomain
    T hposition hphysical hgeometry γ hγ hgap r hr hrb hradius
    εlead hεlead centers row col ρlead L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsourceGeometry hfullTime
    hgeometryc hworking εcarrier ρdet hcell hcarrierCover V hV
    Mproduct Rproduct hproduct hcoverProduct hinit using initialized
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      ball 0 R :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      (ball_subset_ball hbR.le)
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, kCenter, hkCenter, hkDomain,
    T, hposition, hphysical, hgeometry, γ, hγ, hgap, r, hr, hrb, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsourceGeometry, hfullTime,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover, V, hV,
    Mproduct, Rproduct, hproduct, hcoverProduct, ?_⟩
  intro εframe hεframe qext hqcenter hqradius k hk hkD
  have quotientResult := hinit εframe hεframe qext hqcenter hqradius k hk hkD
  choose hz hinc hd ρF ρT qrad s e cF bF cT bT VF LF VT LT
    hboxes ρFext ρText qextRad sext eext cFext bFext cText bText
    VFext LFext VText LText hextBoxes ψF χF ψT χT hcutoffs
    εtransport gtransport hεtransport hgtransport transportCenters
    transportRow transportCol ρtransport Ltransport hρtransport Ωtransport
    hdomains hcover Dq Dt hDq hDt εcommon hεcommon hεcommonr hcommon hinit using quotientResult
  refine ⟨hz, hinc, hd, ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT,
    hboxes, ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, ψF, χF, ψT, χT, hcutoffs,
    εtransport, gtransport, hεtransport, hgtransport, transportCenters,
    transportRow, transportCol, ρtransport, Ltransport, hρtransport, Ωtransport,
    hdomains, hcover, Dq, Dt, hDq, hDt, εcommon, hεcommon, hεcommonr, hcommon, ?_⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  have referenceResult := hinit p orders margin extendedMargin hmargin hextendedMargin cap hcap
  choose θ hθ hθcap hθ1 H hHdomain hHmap hseedResult hcontraction hmean using referenceResult
  choose seed hseedforward hseed hsource using hseedResult
  refine ⟨θ, hθ, hθcap, hθ1, H, hHdomain, hHmap,
    ⟨seed, hseedforward, hseed, ?_, hsource⟩, hcontraction, hmean⟩
  intro incidenceCap hincidenceCap Tm Im Rm Vm rowm colm c₀
    Ωm zCellm ρcm Rcm Mm τleadm Lm aExtra
  exact exists_finite_prescribed_measured_source_raw_inverse hD hn H
    (by simpa only [hHdomain, LocalDomain.chart] using
      (ball_subset_ball hR.le : ball (0 : Euclidean n) R ⊆ ball 0 G₀.domain.chartRadius))
    isBounded_ball Tm Im Ωm
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.1)
    zCellm ρcm Rcm Mm τleadm rowm colm
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.1)
    (fun b l j w hw ↦ by
      have hh := (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.1 hw
      exact ⟨⟨closedBall_subset_ball hbR (interior_subset hh.1.2), hh.1.1⟩, hh.2⟩)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.1.le)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.2.1)
    (fun b l j ↦ (hsourceGeometry ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.2.2.1)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.2.2.2.1)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2)
    (fun b l j ↦ (hgeometryc ⟨b, l⟩ j).2.2.2.2.2.2.2.1)
    (fun b l ↦ hball ⟨b, l⟩) c₀ (fun b l j ↦ (hseed ⟨b, l⟩ j).2)
    Rm Vm (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.1)
    (fun _ _ _ ↦ isOpen_ball)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.1)
    Lm (fun b l j ↦ Mproduct ⟨b, l⟩ j)
    (fun b l j ↦ (hpositive ⟨b, l⟩ j).2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).1)
    (fun b l j ↦ ((hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.2.2.2
      H.map (row ⟨b, l⟩ j) (col ⟨b, l⟩ j) (seed ⟨b, l⟩ j)).1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.1)
    (fun b l j ↦ (hproduct ⟨b, l⟩ j).2.2.2.2.2.2.2.2.2.2.1)
    (fun b l ↦ hcoverProduct ⟨b, l⟩) hincidenceCap aExtra

end JanetCartan.ContinuumInverse
