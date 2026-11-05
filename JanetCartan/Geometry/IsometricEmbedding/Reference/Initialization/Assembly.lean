module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.CarrierReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.CommonTarget

/-!
# Fixed reference initialization

The assembly of `main:prop:seed`, `main:eq:normalized` and `main:eq:seed-small`.
The analytic source, single source dilation, actual carrier menu and quantitative
normal neighborhood precede the target. One normalizing matrix and one common
positive target interval then serve initialization and history smoothing.
Every later positive cap and finite set of accuracies uses these same objects.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan
open GeometricProfile ProtectedFlow
open ProjectedStressFrame ActualCarriers FrozenMenu ActualCarriers.CurrentFullPhase
open ActualCarriers.ConstructedSignedGeometry SignedPairs DefectSmoothing

/-- `main:prop:seed`: unconditional fixed-reference initialization in dimension
at least five. The actual normal and carrier gaps are proved before the target
is introduced. Target normalization, all finite-order linear bounds, continuity
on a compact core containing an open neighborhood of zero, and the actual
history-smoothing estimates share one parameter interval. Initial smallness is
re-derived on every smaller positive cap, so the final dilation can be chosen
after all analytic and frequency thresholds. This constructs the initialization;
it does not assert the later uniform correction step or the final embedding.
The analytic source and finite carrier charts precede the requested finite
full-coefficient orders, positive margins and fixed extension parameters.
One source scale meets the local margins on the compact carrier ball containing
the working chart and the global affine-extension margins with zero lower-order
background (`app:ch_regular:eq:coefficient-extension`). This very same scale and
map are then used for every normalized target and admissible history.
The same carrier family also retains its state-domain containment
in `ball 0 b` and its physical-radius buffers before these choices, for
`ProtectedFlow.exists_primitive_signed_no_return`
(`app:ch_regular:thm:no-return`). -/
theorem exists_fixed_reference_initialization_with_carrier_buffers_and_full_margins {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        (∀ i, 3 * r < (T i).reference.radius) ∧
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
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hphysical, hradius, hchoose⟩ :=
    exists_reference_with_carrier_buffers_and_full_margins hn
  refine ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hphysical, hradius, ?_⟩
  intro p orders margin extendedMargin hmargin hextendedMargin cap hcap
  obtain ⟨ρ, hρ, hρcap, hρ1, G, hmap, hcore, hchart,
    hfull, hsmooth, hextended, hgeometry⟩ :=
    hchoose p orders margin extendedMargin hmargin hextendedMargin cap hcap
  refine ⟨ρ, hρ, hρcap, hρ1, G, hmap, hcore, hchart,
    hfull, hsmooth, hextended, hgeometry, ?_⟩
  intro gtarget Vtarget hV h0 hg kMin horder
  exact exists_normalized_common_target_initialization G hρ hV h0 hg horder

/-- The full-margin initialization constructor with its original interface
(`main:prop:seed`, `main:eq:normalized`, `main:eq:seed-small`). The stronger
`exists_fixed_reference_initialization_with_carrier_buffers_and_full_margins`
also retains the buffers needed by `app:ch_regular:thm:no-return`. -/
theorem exists_fixed_reference_initialization_with_full_margins {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
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
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, _hphysical, _hradius, hchoose⟩ :=
    exists_fixed_reference_initialization_with_carrier_buffers_and_full_margins hn
  exact ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hchoose⟩

/-- `main:prop:seed`: unconditional fixed-reference initialization in dimension
at least five. The actual normal and carrier gaps are proved before the target
is introduced. Target normalization, all finite-order linear bounds, continuity
on a compact core containing an open neighborhood of zero, and the actual
history-smoothing estimates share one parameter interval. Initial smallness is
re-derived on every smaller positive cap, so the final dilation can be chosen
after all analytic and frequency thresholds. This constructs the initialization;
it does not assert the later uniform correction step or the final embedding. -/
theorem exists_fixed_reference_initialization {n : ℕ} (hn : 5 ≤ n) :
    ∃ G₀ : FlatReference n, AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b R : ℝ, 0 < b ∧ b < R ∧ R < G₀.domain.chartRadius ∧
      ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      ∃ r K ε : ℝ, 0 < r ∧ 3 * r < b ∧ 1 ≤ K ∧ 0 < ε ∧ ε ≤ 1 ∧
        K * ε ≤ c / 2 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ G : FlatReference n, G.map = sourceDilation G₀.map ρ ∧
        G.domain.coreRadius = r / 2 ∧ G.domain.chartRadius = r ∧
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
  obtain ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, hchoose⟩ :=
    exists_fixed_reference_initialization_with_full_margins hn
  let p : BallExtension.Parameters (Euclidean n) :=
    ⟨0, b, hb, b / 4, by positivity, by linarith⟩
  obtain ⟨ρ, hρ, _, hρ1, G, hmap, hcore, hchart, _, _, _, hgeometry, htarget⟩ :=
    hchoose p ∅ (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 (by norm_num)
  exact ⟨G₀, hG₀, b, R, hb, hbR, hR, D, c, C, hD, T, r, K, ε,
    hr, hrb, hK, hε, hε1, hKε, ρ, hρ, hρ1, G, hmap, hcore, hchart,
    hgeometry, htarget⟩

end JanetCartan
