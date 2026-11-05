module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.Physical
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.InitializedProtection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.CoefficientBudget

/-!
# Initialized protection with uniform closed finite-chain shoulders

Apply the closed-shoulder construction to the SAME initialized reference,
coefficient extension, comparison charts, angular sets and canonical weights.
All existing no-return and initialization conclusions are retained. The common
width is chosen before the current map; only the finite selector's literal
root-buffer restrictions remain as inputs. This is the propagation consumer
of `app:ch_regular:thm:no-return` for `app:ch_regular:lem:finite-chain`.
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

/-- The actual initialized no-return construction, with a positive uniform
closed-shoulder width at each fixed depth. The coefficient budget, comparison
jets, radial bounds, angular protection and robust source cover are discharged
from the retained construction. Every original conclusion remains available on
these same witnesses. The root family is selected by the arbitrary-accuracy
parent, with the literal primitive root/flow restrictions displayed below;
there is no additional propagated-set hypothesis
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_initialized_signed_no_return_with_closed_shoulders {d : ℕ} (hn : 5 ≤ (d + 1))
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
      (∀ (J : Type) [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
        (η₀ : J → Euclidean d) (εroot G : J → ℝ), (∀ j, 0 ≤ G j) →
        ∀ S : Set (Euclidean (d + 1) × Euclidean (d + 1)), IsCompact S →
        ∀ Bbase : Set (Euclidean (d + 1)), IsCompact Bbase →
        (∀ z ∈ S, z.1 ∈ Bbase) → Bbase ⊆ ball 0 (2 * r) →
        (∀ z ∈ S, z.1 ∈ ball 0 r ∧ z.2 ≠ 0 ∧ normalizedCovector z.2 ∈ Ω₀) →
        ∀ κ Δ : ℝ, 0 < κ → 0 ≤ Δ →
        ∀ V : Set (Euclidean (d + 1) × Euclidean (d + 1)),
          IsOpen V → S ⊆ V → ∀ N : ℕ,
        ∃ δshoulder > (0 : ℝ), ∃ alo > (0 : ℝ), ∃ ahi > alo,
          ∃ B' : Set (Euclidean (d + 1)), IsCompact B' ∧ Bbase ⊆ B' ∧
          ∀ t : ℝ, 0 ≤ t → t ≤ δshoulder → cthickening t S ⊆ V ∧
          ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
          let Qfield := extendedProjectedStress p (lift Q).1;
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsCompact (U j)) → (∀ j, IsCompact (K j)) → IsClosed W →
        (∀ j, U j ⊆ D j) → (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Qfield ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Qfield ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ Bbase) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Qfield (coordinateSplit (i j)) (h j) v|) →
      ∀ (z : J → RootState (Euclidean d)) (Rflow rFlow T : J → ℝ),
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (Rflow j) (rFlow j) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) (rFlow j)) →
        ∀ depth ≤ N, cthickening t
          (bufferedReachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S t depth) ⊆
            (B' ×ˢ FiniteChain.Graph.PhysicalShells.frequencyAnnulus alo ahi) ∩
              physicalProtectedRegion Γin) ∧
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
    (N := embeddingDimension (d + 1)) isOpen_ball
    (isCompact_closedBall (0 : Euclidean (d + 1)) b)
    (closedBall_subset_ball hbB) p (by exact subset_refl _) hδ (2 * r)
  refine ⟨G₀, hG₀, b, B, hb, hbB, hB, D, c, C, hD, T, r₀, hr₀, hr₀b,
    hphysical, hradius, p, rfl, le_rfl, rfl, R, hR, hinj, r, δ, a, A, ε, τ, εx,
    hr, (by linarith), hrp, hδ, ha, hA, hε, hτ, hεx, Ω₀, Ω₁, Γin, Γout,
    hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest, hΩsym₀, hΩsym₁,
    hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, ρ, εw, hρ, hρτ, hεw,
    centers, w, ?_⟩
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
  refine ⟨Z₀, hZ₀, dmap, hdmap, lift, hlift, hlow, hclosure,
    hfreq, hprofile, ?_, hcurrentQ⟩

  intro J _ ℓ η₀ εroot G hG S hS Bbase hBbase hSB hBball hsource κ Δ hκ hΔ V hV hSV N
  obtain ⟨δshoulder, hδshoulder, alo, halo, ahi, hahilo, B', hB', hBbaseB', hshoulders⟩ :=
    exists_uniform_physicalDirectRelation_closed_shoulders ℓ η₀ εroot G hG hS hBbase
      hΓin.isClosed hr hM hcgraph hCgraph hLx hκ hΔ hε hSB hBball
      (fun z hz ↦ ⟨(hsource z hz).1, (hsource z hz).2.1,
        hΩnest (hsource z hz).2.2⟩) hΩΓ hV hSV N
  refine ⟨δshoulder, hδshoulder, alo, halo, ahi, hahilo, B', hB', hBbaseB', ?_⟩
  intro t ht htδ
  refine ⟨(hshoulders t ht htδ).1, ?_⟩
  intro Q Qfield
  have hQfield : ContDiff ℝ ∞ Qfield :=
    contDiff_affineFrameExtension p ((frameOfImmersion isOpen_ball (lift Q)).2.1.mono
      (by exact closedBall_subset_ball hbB))
  intro i h Φ U K Droot W χsource χout hU hK hWclosed hUD hKD hW hDroot hh
    hroot hprimitive hbase hgap z Rflow rFlow Tflow hflow htime hUflow
  obtain ⟨_hEsmooth, _hElow, _hEeq, _hprincipal, _hoperator, _hframeeq, _hflow,
    charts, hderiv, hnorm, _hcompact, _hPchar, hcover, hbuffer, _hrest⟩ := hcurrentQ Q
  exact (hshoulders t ht htδ).2 Qfield hQfield (hbudget (lift Q))
    i h Φ U K Droot W χsource χout hU hK hWclosed hUD hKD hW hDroot hh hroot
    hprimitive hbase hgap z Rflow rFlow Tflow hflow htime hUflow s g charts
    (fun j ↦ by linarith only [hr, hgr j]) hderiv hnorm hcover
    (fun z hz v hv ↦ interior_subset ((hbuffer z hz hv).1))


end JanetCartan.ProtectedFlow
