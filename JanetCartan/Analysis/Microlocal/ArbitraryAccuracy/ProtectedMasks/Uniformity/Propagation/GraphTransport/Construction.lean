module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.UniformTransport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.CoefficientBudget

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.PrimitiveProtection

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PrimitiveProtection
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.SourceMargin
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.Assembly

/-!
# Initialized no-return charts with uniform comparison transport

Assemble `app:ch_regular:thm:no-return` with `main:prop:seed`. The analytic
reference and its actual carrier charts are constructed first. One fixed
extension and one finite selection of comparison rectangles and weights work
for every current map in a primitive neighborhood of the initialized reference.
The source scale simultaneously meets all prescribed finite coefficient margins
and the protection margin; the same reference serves target normalization and
history smoothing. No phase-cover, invariant-graph, signed-gap or reference-margin
hypothesis remains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ArbitraryAccuracy ArbitraryAccuracy.ProtectedMasks RegularSector.Characteristic
open ArbitraryAccuracy.EvolutionIntegratedLocalization
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference
open GeometricProfile DefectSmoothing

/-- Protection of the complete actual signed source product
(`app:ch_regular:thm:no-return`). The analytic reference, carrier menu, fixed
extension, nested angular neighborhoods, common finite rectangles and their four
weights are constructed before source dilation, current maps, high norms,
frequencies and requested accuracy. A single source scale meets every prescribed
finite local/global coefficient margin and the protection margin. Its very same
map and working domain supply target normalization and history smoothing.

The positive angular buffer holds through every finite chain of the selected
weighted factors in either orientation. Every complete support image has a
buffered entire physical segment, and elliptic chains are identities. The full
extended operator agrees with the geometric operator on the physical core and
preserves each coefficient profile. The initialized geometry is chosen from dimension, a fixed low order at least
six, and a positive low-class tolerance. For every fixed positive scale interval
and finite list of primitive root-buffer constants, the graph transport loss is
then chosen before source dilation and the current coefficient field. The C³ budget is constructed from the actual projected-frame neighborhood and
fixed affine extension. The normalized transverse gap, root equation and flow
witnesses in the transport clause are exactly the primitive outputs of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`; they are not estimates
of a propagated shoulder. The retained comparison derivatives, coefficient budget and Hamilton-field
Lipschitz estimate are fully constructed here. The original physical supports,
both orientations, every intermediate point and the original elapsed bound are
preserved (`app:ch_regular:lem:finite-chain`). -/
theorem exists_initialized_signed_no_return_with_graph_transport {d : ℕ} (hn : 5 ≤ (d + 1))
    (m : ℕ) (hm : 6 ≤ m) {εlow : ℝ} (hεlow : 0 < εlow) :
    ∃ G₀ : FlatReference (d + 1), AnalyticOnNhd ℝ G₀.map univ ∧
      ∃ b B : ℝ, 0 < b ∧ ∃ hbB : b < B, B < G₀.domain.chartRadius ∧
      ∃ (D : CoverData (d + 1)) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 B) isOpen_ball,
      ∃ r₀ : ℝ, 0 < r₀ ∧ 3 * r₀ < b ∧
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean (d + 1)) b) ∧
        (∀ i, 3 * r₀ < (T i).physicalRadius) ∧
      ∃ p : BallExtension.Parameters (Euclidean (d + 1)),
      ∃ hp0 : p.center = 0, ∃ hpb : p.radius ≤ b, p.radius = b ∧
    ∃ R : ((j : Fin D.chartCount) × Fin (D.patchCount j)) → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ r δ a A ε τ εx : ℝ, 0 < r ∧ 4 * r < r₀ ∧ 3 * r < p.radius ∧
        0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧ 0 < τ ∧ 0 < εx ∧
      ∃ Ω₀ Ω₁ Γin Γout : Set (Euclidean (d + 1)),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ IsCompact Γin ∧ IsCompact Γout ∧
        Ω₀ ⊆ interior Ω₁ ∧ Ω₁ ⊆ interior Γin ∧ Γin ⊆ interior Γout ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Γout ⊆ (cubeBadSubspaceUnion (d + 1))ᶜ ∧
      ∃ (s : Finset {ξ : Euclidean (d + 1) // ξ ∈ Ω₁ ∧ (frozenSymbol (d + 1)).h (0, ξ) = 0})
        (g : s → ComparisonGeometry (Euclidean (d + 1))),
        (∀ i : s, 3 * r < (g i).radius) ∧
      ∃ cgraph Cgraph Lx : ℝ, 0 < cgraph ∧ 0 < Cgraph ∧ 0 ≤ Lx ∧
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ (J : Type) [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
        (η₀ : J → Euclidean d) (εroot G : J → ℝ), (∀ j, 0 ≤ G j) →
      ∀ κ Δ α β : ℝ, 0 < κ → 0 ≤ Δ → 0 < α → α ≤ β →
      ∃ L : ℝ, 1 ≤ L ∧
      ∀ (orders : Finset ℕ) (margin extendedMargin : ℕ → ℝ),
        (∀ j ∈ orders, 0 < margin j) →
        (∀ j ∈ orders, 0 < extendedMargin j) →
        ∀ cap : ℝ, 0 < cap →
      ∃ σ : ℝ, 0 < σ ∧ σ < cap ∧ σ ≤ 1 ∧
      ∃ Gref : FlatReference (d + 1), Gref.map = sourceDilation G₀.map σ ∧
        Gref.domain.coreRadius = r₀ / 2 ∧ Gref.domain.chartRadius = r₀ ∧
        (∀ j ∈ orders, cNorm (closedBall (0 : Euclidean (d + 1)) b) j
          (geometricReducedCoefficients Gref.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < margin j) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) Gref.map) ∧
        (∀ j ∈ orders, cNorm univ j
          (extendedReducedCoefficients p (fun _ _ ↦ 0) Gref.map -
            reducedCoefficientBackground (fun _ _ ↦ 0)) < extendedMargin j) ∧
      (∀ (gtarget : MetricField (d + 1)) (Vtarget : Set (Euclidean (d + 1))),
        IsOpen Vtarget → (0 : Euclidean (d + 1)) ∈ Vtarget →
        IsRiemannianMetricOn gtarget Vtarget →
        ∀ kMin : ℕ,
          displacementLoss (d + 1) + bandExponent * (1 + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin →
          ∃ M : MetricTensor (d + 1), IsUnit M ∧ coordinatePullback gtarget M 0 = 1 ∧
        ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
          ∃ W : Set (Euclidean (d + 1)), IsOpen W ∧ (0 : Euclidean (d + 1)) ∈ W ∧
            W ⊆ Gref.domain.core (d + 1) ∧
            ∃ B L A C : ℕ → ℝ, (∀ r, 0 < B r) ∧
              (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ A r) ∧ (∀ k, 0 ≤ C k) ∧
              (∀ s ∈ Icc (0 : ℝ) s₀,
                (∀ x ∈ Gref.domain.closureChart (d + 1), coordinateMap M ((s * σ) • x) ∈ Vtarget) ∧
                IsRiemannianMetricOn (scaledMetric (coordinatePullback gtarget M) (s * σ)) (Gref.domain.closureChart (d + 1)) ∧
                ContinuousOn (scaledMetric (coordinatePullback gtarget M) (s * σ)) (Gref.domain.core (d + 1)) ∧
                (∀ r, cNorm (Gref.domain.closureChart (d + 1)) r
                  (scaledMetric (coordinatePullback gtarget M) (s * σ) - inducedMetric Gref.map) ≤ B r * s) ∧
                cNorm (Gref.domain.core (d + 1)) 0
                  (inducedMetric Gref.map - scaledMetric (coordinatePullback gtarget M) (s * σ)) ≤ B 0 * s) ∧
              (∀ cap : ℝ, 0 < cap → cap ≤ s₀ → ∀ η : ℝ, 0 < η →
                ∀ (orders : Finset ℕ) (ε : ℕ → ℝ), (∀ r ∈ orders, 0 < ε r) →
                  ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
                    cNorm (Gref.domain.core (d + 1)) 0
                      (inducedMetric Gref.map - scaledMetric (coordinatePullback gtarget M) (s * σ)) ≤ η ∧
                    ∀ r ∈ orders, cNorm (Gref.domain.closureChart (d + 1)) r
                      (scaledMetric (coordinatePullback gtarget M) (s * σ) - inducedMetric Gref.map) < ε r) ∧
              (∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
                ∀ (j : ℕ) (u : Fin j → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
                  (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
                let R := iterationScale R₀ growthExponent j
                let δ := R ^ (-(k : ℝ))
                let gs := scaledMetric (coordinatePullback gtarget M) (s * σ)
                let e := historyDefect gs Gref.map u
                cNorm (Gref.domain.core (d + 1)) 0 e ≤ δ ^ 2 →
                let eR := smoothedHistoryDefect Gref.domain R gs Gref.map u
                IsSmoothPeriodic eR ∧ HasFourierSupport (2 * R) eR ∧
                ((∀ x ∈ Gref.domain.core (d + 1), (gs x).IsSymm) → ∀ z, (eR z).IsSymm) ∧
                (∀ r (K : Set (Euclidean (d + 1))),
                  cNorm K r (periodicLift eR) + periodicSobolevNorm (r : ℝ) eR ≤
                    L r * δ ^ 2 * R ^ r) ∧
                (∀ r (K : Set (Euclidean (d + 1))),
                  cNorm K r (periodicLift
                      (normalizedHistorySource Gref.domain R δ gs Gref.map u)) +
                    periodicSobolevNorm (r : ℝ)
                      (normalizedHistorySource Gref.domain R δ gs Gref.map u) ≤
                    A r * R ^ ((r : ℝ) - 2 * forcingExponent (d + 1))) ∧
                cNorm (Gref.domain.core (d + 1)) 0 (e - periodicLift eR) ≤
                  C k * δ * R ^ (-2 * (k : ℝ)) ∧
                (∀ x ∈ Gref.domain.core (d + 1), ‖periodicLift eR x - e x‖ ≤
                  C k * δ * R ^ (-2 * (k : ℝ))))) ∧
      ∃ Z₀ : Euclidean (d + 1) → Fin (d + 1) × Fin (d + 1) → ℝ, ContDiff ℝ ∞ Z₀ ∧
      ∃ dmap > (0 : ℝ),
      ∃ lift : PrimitiveMapNeighborhood Gref B (m + 2) dmap →
        ProjectedImmersionNeighborhood (embeddingDimension (d + 1)) (ball 0 B) (closedBall 0 b) δ,
      (∀ F, (lift F).1 = F.1) ∧
      ∃ hlow : ∀ (Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap) i,
        cNorm (closedBall (0 : Euclidean (d + 1)) (T i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress (lift Q).1 - fun _ ↦ cubeStress (d + 1)) < (T i).family.threshold,
      let family := fun z : PrimitiveMapNeighborhood Gref B (m + 2) dmap × closedBall (0 : Euclidean (d + 1)) r ↦
        currentGroup T id R (ProjectedStressFrame.projectedStress (lift z.1).1)
          (frameOfImmersion isOpen_ball (lift z.1)).2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D id)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair ((j : Fin D.chartCount) × Fin (D.patchCount j)) (Euclidean 3) (groupCube D id)),
        (∀ L ∈ cubeBadSubspaces (d + 1), a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      (∀ (Dprofile : ℕ → ℝ) (order : ℕ), ∃ Cprofile : ℕ → ℝ,
        (∀ j, 0 < Cprofile j) ∧ ∀ slow : ℝ, 1 ≤ slow →
          ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
          HasDerivativeProfile (closedBall p.center p.radius)
            (geometricReducedCoefficients Q.1) order slow Dprofile →
          HasDerivativeProfile (closedBall (0 : Euclidean (d + 1)) (3 * r))
            (extendedReducedCoefficients p Z₀ Q.1) order slow Cprofile) ∧
      ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
        ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ Q.1) ∧
        cNorm univ m
          (extendedReducedCoefficients p Z₀ Q.1 - reducedCoefficientBackground Z₀) < εlow ∧
        EqOn (extendedReducedCoefficients p Z₀ Q.1) (geometricReducedCoefficients Q.1)
          (closedBall 0 (3 * r)) ∧
        (∀ x a i k, extendedReducedCoefficients p Z₀ Q.1 x (.inl (a, i, k)) =
          extendedProjectedStress p Q.1 x i a k) ∧
        (∀ u x, x ∈ closedBall 0 (3 * r) → ∀ i,
          reducedCoefficientOperator (extendedReducedCoefficients p Z₀ Q.1) u x i =
            NullTransport.reducedOperator Q.1 (ProjectedStressFrame.projectedStress Q.1) u x i) ∧
        EqOn (extendedProjectedStress p Q.1) (ProjectedStressFrame.projectedStress Q.1) (closedBall 0 (3 * r)) ∧
        let H := normalizedHomogeneousSymbol isOpen_univ (extendedProjectedStress p (lift Q).1)
          (contDiff_affineFrameExtension p ((frameOfImmersion isOpen_ball (lift Q)).2.1.mono
            (by rw [hp0]; exact closedBall_subset_ball (hpb.trans_lt hbB)))).contDiffOn;
        (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
          (Φ : HamiltonFlow H V) (u : InitialData V) (t₀ : ℝ),
          u ∈ Φ.parameters →
          (Φ.position (t₀, u), Φ.momentum (t₀, u)) ∈ closedBall 0 r ×ˢ Ω₁ →
          (∀ t ∈ Icc (-τ) τ, t₀ + t ∈ Φ.time) →
          ∀ t ∈ Icc (-τ) τ,
            closedBall (Φ.position (t₀ + t, u)) εx ⊆ ball 0 (2 * r)) ∧
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ i : s, ∀ η ∈ (g i).parameters, ∀ x ∈ closedBall 0 (2 * r),
            ‖fderiv ℝ ((charts i).gradientMap η) x‖ ≤ Lx) ∧
          (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
            cgraph ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ Cgraph) ∧
          (∀ j : s, ∀ η ∈ (g j).parameters, ∀ x ∈ closedBall 0 (2 * r),
            ∀ y ∈ closedBall 0 (2 * r),
              ‖(charts j).gradientMap η x - (charts j).gradientMap η y‖ ≤ Lx * dist x y) ∧
          cNorm (closedBall 0 (2 * r)) 3 (extendedProjectedStress p (lift Q).1) ≤ M ∧
          (∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
              (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
              (U K Droot : J → Set (RootState (Euclidean d)))
              (W : Set (Euclidean (d + 1)))
              (χsource χout : J → Euclidean (d + 1) → ℂ),
              (∀ j, IsOpen (Droot j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (Droot j)) →
              (∀ j v, v ∈ Droot j → v.2.2 ≠ 0 ∧
                determinant (extendedProjectedStress p (lift Q).1
                  ((coordinateSplit (i j)).symm (v.1, v.2.1)))
                  ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
                fderiv ℝ (determinant (extendedProjectedStress p (lift Q).1
                  ((coordinateSplit (i j)).symm (v.1, v.2.1))))
                  ((coordinateSplit (i j)).symm (h j v, v.2.2))
                  ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
              (∀ j, K j ⊆ Droot j) → W ⊆ closedBall 0 (2 * r) →
              (∀ j v, v ∈ K j → v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
                (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
              (∀ j v, v ∈ K j → κ ≤
                |pencilRootSpeed (extendedProjectedStress p (lift Q).1)
                  (coordinateSplit (i j)) (h j) v|) →
            ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow Tflow : J → ℝ),
              (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
                (z j) (Rflow j) (rFlow j) (Tflow j) (Φ j)) →
              (∀ j, Δ < Tflow j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
            ∀ j : s, ∀ η ∈ (g j).parameters, ∀ scale ∈ Icc α β, ∀ u v,
              physicalDirectRelation i h Φ U K W χsource χout Δ u v →
              ‖v.2 - scale • (charts j).gradientMap η v.1‖ ≤
                L * ‖u.2 - scale • (charts j).gradientMap η u.1‖) ∧
          IsCompact (normalizedGraphImage (ComparisonChart.familyGradient charts)
            (closedBall 0 (2 * r)) univ) ∧
          let P := positiveConicLift (ComparisonChart.familyGradient charts)
            (ball 0 (2 * r)) univ;
          P ⊆ H.domain ∩ {z | H.h z = 0} ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, H.h z = 0 → z ∈ P) ∧
          (∀ z ∈ P, closedBall (normalizedCovector z.2) ε ⊆
            interior Γin \ cubeBadSubspaceUnion (d + 1)) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion (d + 1)) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εw ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ v k,
            PositiveConicChain (selectedFactorRelation charts w) z v k →
              closedBall (normalizedCovector v.2) ε ⊆
                interior Γin \ cubeBadSubspaceUnion (d + 1)) ∧
          (∀ z v k, PositiveConicChain (selectedFactorRelation charts w) z v k →
            H.h z ≠ 0 → z = v) ∧
          (∀ i : s, ∀ q : centers i, ∀ backward Ksource,
            Ksource ⊆ (w i q).sourceProduct → ∀ v,
            v ∈ completeImage backward (w i q).physicalSupport Ksource →
            ∃ u ∈ Ksource,
              (canonicalState (charts i).flow u = canonicalState (charts i).flow v ∨
                CompleteCharacteristicSegment H (ball 0 (2 * r))
                  (canonicalState (charts i).flow u) (canonicalState (charts i).flow v)) ∧
              ∀ t ∈ Icc (min u.1.1 v.1.1) (max u.1.1 v.1.1),
                closedBall (canonicalState (charts i).flow ((t, u.1.2), u.2)).1 εw ⊆
                  ball 0 (2 * r)) := by
  obtain ⟨G₀, hG₀, b, B, hb, hbB, hB, D, c, C, hD, T, r₀, K, e,
    hr₀, hr₀b, _hK, _he, _he1, _hKe, hphysical, hradius, hchoose⟩ :=
    exists_fixed_reference_initialization_with_carrier_buffers_and_full_margins hn
  let p : BallExtension.Parameters (Euclidean (d + 1)) :=
    ⟨0, b, hb, b / 4, by positivity, by linarith⟩
  have hball (i) : closedBall (0 : Euclidean (d + 1)) (T i).data.localReference.stateRadius ⊆
      closedBall 0 b :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      ball_subset_closedBall
  have hradius' (i) : r₀ / 4 < (T i).physicalRadius := by
    have hi := hradius i
    change 3 * r₀ < (T i).physicalRadius at hi
    linarith
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx,
    ρ, εw, hρ, hρτ, hεw, centers, w, ηref, hηref, hcurrent⟩ :=
    exists_primitive_signed_no_return_with_graph_bounds hn hD hbB T
      ((j : Fin D.chartCount) × Fin (D.patchCount j)) id hball p rfl le_rfl
      (show 0 < r₀ / 4 by positivity) hradius' m hm hεlow
  obtain ⟨capref, hcapref, _hcapref1, hmarginref⟩ :=
    exists_source_dilation_protected_reference_margin G₀ (b := b) m hηref
  obtain ⟨M, hM, hbudget⟩ := exists_uniform_extendedProjectedStress_cNorm_three_bound
    (N := embeddingDimension (d + 1)) isOpen_ball (isCompact_closedBall (0 : Euclidean (d + 1)) b)
    (closedBall_subset_ball hbB) p (by exact subset_refl _) hδ (2 * r)
  refine ⟨G₀, hG₀, b, B, hb, hbB, hB, D, c, C, hD, T, r₀, hr₀, hr₀b,
    hphysical, hradius, p, rfl, le_rfl, rfl, R, hR, hinj, r, δ, a, A, ε, τ, εx,
    hr, (by linarith), hrp, hδ, ha, hA, hε, hτ, hεx, Ω₀, Ω₁, Γin, Γout,
    hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest, hΩsym₀, hΩsym₁,
    hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, ρ, εw, hρ, hρτ, hεw,
    centers, w, M, hM, ?_⟩
  intro J _ ℓ η₀ εroot G hG κ Δ α β hκ hΔ hα hαβ
  obtain ⟨L, hL, htransport⟩ := exists_uniform_physicalDirectRelation_comparison_transport
    ℓ η₀ εroot G hG (show 0 < 2 * r by positivity) hM hcgraph hCgraph hLx
      hκ hΔ hα hαβ
  refine ⟨L, hL, ?_⟩
  intro orders margin extendedMargin hmargin hextendedMargin cap hcap
  obtain ⟨σ, hσ, hσcap, hσ1, Gref, hmap, hcore, hchart,
    hfull, hsmooth, hextended, _hgeometry, htarget⟩ :=
    hchoose p orders margin extendedMargin hmargin hextendedMargin
      (min cap capref) (lt_min hcap hcapref)
  refine ⟨σ, hσ, hσcap.trans_le (min_le_left _ _), hσ1, Gref, hmap,
    hcore, hchart, hfull, hsmooth, hextended, htarget, ?_⟩
  have href := hmarginref σ ⟨hσ, hσcap.le.trans (min_le_right _ _)⟩
  have hprotected := hcurrent (sourceDilationReference G₀ hσ hσ1) hB href
  unfold PrimitiveMapNeighborhood at hprotected ⊢
  rw [hmap]
  obtain ⟨Z₀, hZ₀, dmap, hdmap, lift, hlift, hlow, hclosure, hfreq,
    hprofile, hcurrentQ⟩ := hprotected
  refine ⟨Z₀, hZ₀, dmap, hdmap, lift, hlift, hlow, hclosure, hfreq, hprofile, ?_⟩
  intro Q
  obtain ⟨hEsmooth, hElow, hEeq, hprincipal, hoperator, hframeeq, hflow,
    charts, hderiv, hnorm, hrest⟩ := hcurrentQ Q
  refine ⟨hEsmooth, hElow, hEeq, hprincipal, hoperator, hframeeq, hflow,
    charts, hderiv, hnorm, ?_, hbudget (lift Q), ?_, hrest⟩
  · intro j η hη x hx y hy
    exact comparisonChart_gradient_dist_le_of_derivative_bound (charts j) hη
      (by linarith [hgr j]) (hderiv j η hη) hx hy
  · intro i h Φ U K Droot W χsource χout hDroot hh hroot hKD hW
      hsection hgap z Rflow rFlow Tflow hΦ htime hU j η hη scale hscale u v huv
    have hE := contDiff_affineFrameExtension p
      ((frameOfImmersion isOpen_ball (lift Q)).2.1.mono
        (by rw [show p.center = 0 from rfl]; exact closedBall_subset_ball hbB))
    exact (htransport (extendedProjectedStress p (lift Q).1) hE (hbudget (lift Q))
      i h Φ U K Droot W χsource χout hDroot hh hroot hKD hW hsection hgap
      z Rflow rFlow Tflow hΦ htime hU (g j) (charts j)
      (by linarith [hgr j]) (hderiv j)
      (fun η hη x hx ↦ hnorm ⟨j, ⟨η, hη⟩⟩ x hx) η hη).2 scale hscale u v huv

end JanetCartan.ProtectedFlow
