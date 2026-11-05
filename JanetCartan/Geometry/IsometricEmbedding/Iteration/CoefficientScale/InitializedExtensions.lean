module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FixedReferenceExtensions

/-!
# Joint extensions on the same initialized history

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, intersect the
all-small-source extension cap with the already assembled initializer. This
retains its map, finite Hamilton family, leading amplitudes, quotient profiles,
finite margins, target normalization and smoothing conclusions. The fixed
extension operators and their bounds now apply to exactly those histories.

The two finite covers share a positive physical neighborhood chosen before the
source scale. Initial scalar inputs remain explicit: the actual positive
background and finite preparation still have to supply them. This theorem
closes the common-reference extension obligation, not that scalar construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open GeometricProfile ProtectedFlow ProjectedStressFrame ActualCarriers FrozenMenu CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing
open NullTransport ActualFlow FlowAmplitude AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates JointExtensions

/-- `main:prop:seed`, `main:prop:current-scale`, `app:eq:uniform-high-coeff`:
one initializer-selected reference supports the previous leading and quotient
profiles together with the fixed global geometric, Hamilton, quotient and
transport extensions. All previous initialization conclusions are retained.
The extension source cap is imposed before choosing the reference, and its
literal map equality supplies the larger analytic domain. The finite covers
share a fixed positive physical neighborhood before any source or history
choice. The extension reserves are two, three, six and five; scalar and full
reconstruction reserves remain thirteen and fourteen. No current coefficient
profile is assumed. The prepared initial scalar remains the obligation of the
actual positive-background and finite-preparation producers. -/
theorem exists_initialized_history_profiles_and_joint_extensions {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ) (hD : D.IsValid c C),
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        (∀ i, 3 * r < (T i).reference.radius) ∧
    ∃ εlead : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ, (∀ i, 0 < εlead i) ∧
    ∃ centers : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → Finset (parameterCube (D.patches i.1 i.2).radius),
    ∃ row col : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → Fin n,
    ∃ ρlead L τ Rc τc Mc rcomp δcomp σcover : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) → centers i → ℝ,
      (∀ i j, 0 < ρlead i j ∧ 0 < L i j ∧ 0 < τ i j ∧ 0 < Rc i j ∧ 0 < τc i j ∧
        0 < Mc i j ∧ 0 < rcomp i j ∧ 0 < δcomp i j ∧ 0 < σcover i j) ∧
    ∃ V : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → Set (Euclidean 3 × Euclidean (n - 1)),
      (∀ i, IsOpen (V i) ∧
        (∀ z ∈ parameterCube (D.patches i.1 i.2).radius, (z, (T i).reference.spatialPatch z) ∈ V i) ∧
        (ball (0 : Euclidean n) (εlead i) ×ˢ V i ⊆
          ⋃ j : centers i, closedBall ((0 : Euclidean n),
            (j.1.1, (T i).reference.spatialPatch j.1.1)) (σcover i j))) ∧
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
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.domain.coreRadius = r / 2 ∧ G.domain.chartRadius = r ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean n) b) j
          (geometricReducedCoefficients G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) G.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
      (∃ δ C₀ κ εframe : ℝ, 0 < δ ∧ 0 < C₀ ∧ 0 < κ ∧ 0 < εframe ∧
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
          κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖) ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 R),
      ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress G.map - fun _ ↦ cubeStress n) < (T i).family.threshold,
        (∀ i, ∃ I : CarrierFullPhaseInput (T i).reference
            (normalizedHomogeneousSymbol isOpen_ball (projectedStress G.map) hQ) (ε / 2),
          I.flow = (T i).family.flow ⟨projectedStress G.map, hQ, hlow i⟩ ∧
          HEq I.chart ((T i).currentChart ⟨projectedStress G.map, hQ, hlow i⟩) ∧
          IsAssembledCarrierPhase (T i).reference I (projectedStress G.map)
            ((T i).carrier ⟨projectedStress G.map, hQ, hlow i⟩) r K (ε / 2) ∧
          (∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
            ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            ∀ w ∈ parameterCube (D.patches i.1 i.2).radius, ∀ L ∈ cubeBadSubspaces n,
              (c / 2) * ‖z - w‖ ≤ ‖Lᗮ.orthogonalProjectionOnto
                ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z -
                  (T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x w)‖)) ∧
        (∃ arank > (0 : ℝ), ∀ i, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
          ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
            arank ≤ ‖(pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).adjugate‖ ∧
            (pencil (projectedStress G.map x)
              ((T i).carrierGradient ⟨projectedStress G.map, hQ, hlow i⟩ x z)).rank = n - 1) ∧
        (∃ label : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ,
          (∀ i, 1 ≤ label i) ∧ Function.Injective label ∧
          ∃ γ a A asing csing ds M : ℝ,
            0 < γ ∧ 0 < a ∧ 0 < A ∧ 0 < asing ∧ 0 < csing ∧ 0 < ds ∧ 0 < M ∧
            IsCompact (angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, -v ∈ angularSet n γ) ∧
            (∀ v ∈ angularSet n γ, ∀ w ∈ cubeBadSubspaceUnion n, γ ≤ dist v w) ∧
            Disjoint (angularSet n γ) (cubeBadSubspaceUnion n) ∧
            (closure (directionSet
              (fun x : closedBall (0 : Euclidean n) r ↦
                currentGroup T id label (projectedStress G.map) hQ hlow x)
              (groupCube D id)) ⊆ angularSet n γ) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) r,
              ∀ q : Pair ((j : Fin D.chartCount) × Fin (D.patchCount j))
                  (Euclidean 3) (groupCube D id),
                (∀ L ∈ cubeBadSubspaces n,
                  a * q.beat ≤ ‖projectAway L
                    (q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x))‖) ∧
                q.vector (currentGroup T id label (projectedStress G.map) hQ hlow x) ≠ 0 ∧
                (∀ lam : ℝ, 0 ≤ lam →
                  a * (lam * q.beat) ≤ ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ∧
                  ‖lam • q.vector
                    (currentGroup T id label (projectedStress G.map) hQ hlow x)‖ ≤
                    A * (lam * q.beat))) ∧
            (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v ∈ angularSet n γ,
              asing ≤ ‖(pencil (projectedStress G.map x) v).adjugate‖ ∧
              n - 1 ≤ (pencil (projectedStress G.map x) v).rank ∧
              ‖pencil (projectedStress G.map x) v‖ ≤ M ∧
              csing ≤ (pencil (projectedStress G.map x) v).toEuclideanLin.singularValues
                (⟨n - 2, by omega⟩ : Fin n) ∧
              (determinant (projectedStress G.map x) v = 0 →
                ds ≤ ‖fderiv ℝ (determinant (projectedStress G.map x)) v‖))) ∧
        ∃ Rroot : IncidenceRefinement D, Rroot.IsValid ∧
          ∃ cr Br εroot cdet : ℝ, 0 < cr ∧ 0 < Br ∧ 0 < εroot ∧ 0 < cdet ∧
          ∃ g : (j : Fin Rroot.chartCount) → Fin (D.patchCount (Rroot.sourceChart j)) →
              Euclidean n × Euclidean n → ℝ,
            IsConstructedIncidenceRootFamily D Rroot r cr Br εroot (projectedStress G.map)
              (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress G.map, hQ, hlow ⟨j, a⟩⟩) g ∧
            ∀ j, ∀ x ∈ closedBall (0 : Euclidean n) (2 * r),
              ∀ k ∈ closedBall (Rroot.center j) (Rroot.radius j), ∀ s : Euclidean n,
                cdet * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (projectedStress G.map x) k) s‖ ^ 2 +
                  ∑ a, ⟪quadratic (projectedStress G.map x)
                    ((T ⟨Rroot.sourceChart j, a⟩).carrierGradient
                      ⟨projectedStress G.map, hQ, hlow ⟨Rroot.sourceChart j, a⟩⟩ x
                      (incidenceParameter (D.roots (Rroot.sourceChart j) a (Rroot.center j))
                        (g j a (x, k)))), s⟫_ℝ ^ 2) ∧
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
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
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
        cNorm (closedBall 0 b) 6 (projectedStress F - fun _ ↦ cubeStress n) < ε ∧
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
                  C k * δ * R ^ (-2 * (k : ℝ)))) := by
  classical
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hphysical, hradius, hchoose⟩ :=
    exists_fixed_reference_initialization_with_carrier_buffers_and_full_margins hn
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 b :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      ball_subset_closedBall
  obtain ⟨εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp,
    σcover, hpositive, V, hV, capLead, hcapLead, _, hlead⟩ :=
    exists_source_scale_cap_for_history_full_modulation
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) hn G₀ hb hbR hR
      (fun i ↦ D.patches i.1 i.2) (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hphysical, hradius,
    εlead, hεlead, centers, row, col, ρlead, L, τ, Rc, τc, Mc, rcomp, δcomp,
    σcover, hpositive, V, hV, ?_⟩
  intro qext hqcenter hqradius k hk hkD
  have hz (i) := ((hD.2.2.2.2.1 i.1 i.2).2.2.1 (k i) (hkD i)).1
  have hinc (i) := ((hD.2.2.2.2.1 i.1 i.2).2.2.1 (k i) (hkD i)).2.2.2
  have hd (i) : fderiv ℝ (fun w ↦ incidence (k i)
      ((D.patches i.1 i.2).toFun w)) (D.roots i.1 i.2 (k i))
      (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le
      ((hD.2.2.2.2.1 i.1 i.2).2.2.2 (k i) (hkD i) _ (fun j ↦ (hz i j).le)))
  obtain ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, hboxes,
    capQ, hcapQ, _, hquotient⟩ :=
    FixedReferenceProfiles.exists_source_scale_cap_for_fixed_reference_history_profiles
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) G₀ hb hbR hR
      qext hqcenter hqradius (fun i ↦ D.patches i.1 i.2)
      (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
      (fun i ↦ D.roots i.1 i.2 (k i)) k hz hk hinc hd
  obtain ⟨ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, ψF, χF, ψT, χT, hcutoffs,
    εtransport, gtransport, hεtransport, hgtransport,
    transportCenters, transportRow, transportCol, ρtransport, Ltransport,
    hρtransport, Ωtransport, hdomains, hcover, Dq, Dt, hDq, hDt,
    capExt, hcapExt, _, hext⟩ :=
    exists_source_scale_cap_for_fixed_reference_joint_extensions
      (I := (j : Fin D.chartCount) × Fin (D.patchCount j)) hn G₀ hb hbR hR
      qext hqcenter hqradius (fun i ↦ D.patches i.1 i.2)
      (fun i ↦ (hD.2.2.2.2.1 i.1 i.2).1) T hball
      (fun i ↦ D.roots i.1 i.2 (k i)) k hz hk hinc hd hε
  obtain ⟨εsmall, _, _, hεsmall, _, _, _, hsmall⟩ := exists_common_phase_buffers
    (fun i ↦ min (εlead i) εtransport) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun i ↦ lt_min (hεlead i) hεtransport) (fun _ ↦ zero_lt_one)
  let εcommon := min εsmall (r / 2)
  have hεcommon : 0 < εcommon := lt_min hεsmall (half_pos hr)
  have hcommonLead (i) : εcommon ≤ εlead i := by
    have h := (hsmall i).1.trans_le (min_le_left _ _)
    have hle : εcommon ≤ εsmall := min_le_left _ _
    linarith only [h, hle, hεsmall]
  have hcommonTransport (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) :
      εcommon ≤ εtransport := by
    have h := (hsmall i).1.trans_le (min_le_right _ _)
    have hle : εcommon ≤ εsmall := min_le_left _ _
    linarith only [h, hle, hεsmall]
  refine ⟨hz, hinc, hd, ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT,
    hboxes, ρFext, ρText, qextRad, sext, eext, cFext, bFext, cText, bText,
    VFext, LFext, VText, LText, hextBoxes, ψF, χF, ψT, χT, hcutoffs,
    εtransport, gtransport, hεtransport, hgtransport,
    transportCenters, transportRow, transportCol, ρtransport, Ltransport,
    hρtransport, Ωtransport, hdomains, hcover, Dq, Dt, hDq, hDt,
    εcommon, hεcommon, (min_le_right _ _).trans_lt (half_lt_self hr), ?_, ?_⟩
  · intro i
    exact ⟨(prod_mono (ball_subset_ball (hcommonLead i)) Subset.rfl).trans (hV i).2.2,
      (prod_mono (closedBall_subset_closedBall (hcommonTransport i)) Subset.rfl).trans
        (hcover i)⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  obtain ⟨ρ, hρ, hρcap, hρ1, G, hmap, hcore, hchart,
    hfull, hsmooth, hextended, hgeometry, htarget⟩ :=
    hchoose p orders margin extendedMargin hmargin hextendedMargin
      (min cap (min capLead (min capQ capExt)))
      (lt_min hcap (lt_min hcapLead (lt_min hcapQ hcapExt)))
  have hleadCap : ρ ≤ capLead :=
    (hρcap.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hquotientCap : ρ ≤ capQ :=
    ((hρcap.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hextCap : ρ ≤ capExt :=
    ((hρcap.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  refine ⟨ρ, hρ, hρcap.trans_le (min_le_left _ _), hρ1, G, hmap, hcore, hchart,
    hfull, hsmooth, hextended, hgeometry, hlead ρ hρ hleadCap G hmap,
    hquotient ρ hρ hquotientCap G hmap, hext ρ hρ hextCap G hmap, htarget⟩

end JanetCartan.CurrentCoefficientProfiles
