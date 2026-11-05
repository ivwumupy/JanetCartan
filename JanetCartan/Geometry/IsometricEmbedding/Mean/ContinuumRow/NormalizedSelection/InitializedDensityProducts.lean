module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.InitializedCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.DensityProducts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonSeed
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.SourceFamily

/-!
# Original density products on the actual common initializer

Apply the uniform retained product construction to the original initializer's
cells, exact times and full-modulation working buffers. The physical radii and
forward constants precede the reference, target and finite histories. The
entire original parameter balls and incidence coverage remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ContinuumRow.NormalizedSelection
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates CurrentCoefficientProfiles CurrentCoefficientProfiles.JointExtensions
open NormalizedBackground NormalizedBackground.SourceGeometry FrozenPhaseReference HamiltonPhase ContinuumRow
open ContinuumNormal.CarrierVariation.FamilyInputs

open PositiveReference PositiveReference.FlowConstruction
open CanonicalCarrier

/-- Construct the original density products on the SAME actual initialized
cells as the normalized source charts. The forward constant, coefficient-domain
admission, inverse smoothness, original `L/16` label range and every positive
source range are conclusions for every chart on those retained parameters.
Only physical radii shrink; scalar centers, parameter balls, coefficient
minors, original scalar class and the full incidence cover are preserved.
All original reference, target, history and weight clauses remain attached to
these choices. Consumers: `exists_finite_measured_incidence_row`,
`exists_finite_seed_source_density_carriers_with_normalized_actions` and
`ActualConstruction.exists_initialScale_for_realized_retained_history_coercivity`
(`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-normalized`,
`app:ch_waves:eq:joint-tame`, `new:sec:order-of-choices`). -/
theorem exists_common_initializer_with_normalized_charts_and_density_products {n : ℕ} (hn : 5 ≤ n) :
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
                  EqOn (phase ((T a).currentChart Qσ).coordinates)
                    (sourcePhase (phase ((T a).currentChart (Q a)).coordinates) σ) (T a).target ∧
                  (∀ m : ℕ, EqOn (iteratedFDeriv ℝ m (phase ((T a).currentChart Qσ).coordinates))
                    (iteratedFDeriv ℝ m
                      (sourcePhase (phase ((T a).currentChart (Q a)).coordinates) σ)) (T a).target) ∧
                  (let S := fun p : Euclidean n × Euclidean (n - 1) ↦
                      phase ((T a).currentChart (Q a)).coordinates (p.1, (0, p.2))
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
  have initialized := exists_common_initializer_with_normalized_charts hn
  choose G₀ hG₀ b R hb hbR hR D c C hD kCenter hkCenter hkDomain
    T hposition hphysical hgeometry γ hγ hgap r hr hrb hradius
    εlead hεlead centers row col ρlead L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsourceGeometry hfullTime
    hgeometryc hworking εcarrier ρdet hcell hcarrierCover V hV hinit using initialized
  have productResult (i) (j : centers i) :=
    exists_retained_density_product_geometry (N := embeddingDimension n) (T i) j.1.1
      (hpositive i j).2.1 (hpositive i j).2.2.2.1 (hgeometryc i j).2.1.le
      (lt_min (hcell i j).1 (lt_min (T i).physicalRadius_pos (hb.trans hbR)))
      (hgeometryc i j).2.2.2.2.2.2.2.2.1
      (hgeometryc i j).2.2.2.1 (isCompact_closedBall _ _)
      (hgeometryc i j).2.2.2.2.1 (hgeometryc i j).2.2.2.2.2.2.2.1
      (hpositive i j).2.2.2.2.2.2.2.2 (hworking i j).1
      (ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j))
      ((hcell i j).2.2.1.mono_left (Set.prod_mono
        (ball_subset_ball (min_le_left (εcarrier i j) (min (T i).physicalRadius R))) Subset.rfl))
      ((hcell i j).2.2.2.1.mono_left (Set.prod_mono
        (ball_subset_ball (min_le_left (εcarrier i j) (min (T i).physicalRadius R))) Subset.rfl))
      (hrc i j)
  choose Mproduct Rproduct hMproduct hRproduct hRproductCap hRproductTime
    hzero hflow hlabel htime hcharts using productResult
  have hRproductε (i) (j : centers i) : Rproduct i j ≤ εcarrier i j :=
    (hRproductCap i j).trans (min_le_left _ _)
  have hRproductPhysical (i) (j : centers i) : Rproduct i j ≤ (T i).physicalRadius :=
    (hRproductCap i j).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRproductU (i) (j : centers i) : ball (0 : Euclidean n) (Rproduct i j) ⊆ ball 0 R :=
    ball_subset_ball ((hRproductCap i j).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hVP (i) (j : centers i) :
      ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) ⊆
        CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * (D.patches i.1 i.2).radius / 2) := by
    intro z hz
    exact ((hcell i j).2.2.2.2.2.1
      (show ((0 : Euclidean n), z) ∈ ball 0 (εcarrier i j) ×ˢ
        ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) from
          ⟨mem_ball_self (hcell i j).1, hz⟩)).2
  have hcoverProduct (i) (z) (hz : z ∈ parameterCube (D.patches i.1 i.2).radius) :
      ∃ j : centers i, ((0 : Euclidean n), (z 0, spectatorCenter z)) ∈
        ball (0 : Euclidean n) (Rproduct i j) ×ˢ
          ball (j.1.1 0, spectatorCenter j.1.1) (εcarrier i j) := by
    obtain ⟨j, hj⟩ := hcarrierCover i z hz
    exact ⟨j, mem_ball_self (hRproduct i j), hj.2⟩
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, kCenter, hkCenter, hkDomain,
    T, hposition, hphysical, hgeometry, γ, hγ, hgap, r, hr, hrb, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsourceGeometry, hfullTime,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover, V, hV,
    Mproduct, Rproduct, ?_, hcoverProduct, hinit⟩
  intro i j
  refine ⟨hMproduct i j, hRproduct i j, hRproductε i j, hRproductPhysical i j,
    hRproductU i j, hRproductTime i j,
    Set.prod_mono (ball_subset_ball (hRproductε i j)) Subset.rfl,
    ?_, hVP i j, hflow i j, hlabel i j, htime i j, hcharts i j⟩
  intro z
  simp only [mem_prod, mem_ball_self (hRproduct i j), mem_ball_self (hcell i j).1, true_and]

end JanetCartan.ContinuumRow.NormalizedSelection
