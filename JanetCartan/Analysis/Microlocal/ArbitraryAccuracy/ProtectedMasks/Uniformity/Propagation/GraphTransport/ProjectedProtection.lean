module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.SignedProtection

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.UniformSigned
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ProjectedProtection

/-!
# Uniform signed protection for the literal projected frame

Specialize the constructed uniform factors to the immersion's projected stress
frame, retaining the same carrier charts (`app:ch_regular:thm:no-return`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference

/-- The fixed rectangles and all four weights protect the complete signed
product of the literal projected frame. Every finite chain, both orientations,
limiting chord and true beat is retained (`app:ch_regular:thm:no-return`). -/
theorem exists_projected_signed_uniform_protection_with_graph_bounds {n N : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    (hpK : closedBall p.center p.radius ⊆ K)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hradius : ∀ i, r₀ < (T i).physicalRadius) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ r δ a A ε τ εx : ℝ, 0 < r ∧ r < r₀ ∧ 3 * r < p.radius ∧
        0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧ 0 < τ ∧ 0 < εx ∧
      ∃ Ω₀ Ω₁ Γin Γout : Set (Euclidean n),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ IsCompact Γin ∧ IsCompact Γout ∧
        Ω₀ ⊆ interior Ω₁ ∧ Ω₁ ⊆ interior Γin ∧ Γin ⊆ interior Γout ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Γout ⊆ (cubeBadSubspaceUnion n)ᶜ ∧
      ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω₁ ∧ (frozenSymbol n).h (0, ξ) = 0})
        (g : s → ComparisonGeometry (Euclidean n)),
        (∀ i : s, 3 * r < (g i).radius) ∧
      ∃ cgraph Cgraph Lx : ℝ, 0 < cgraph ∧ 0 < Cgraph ∧ 0 ≤ Lx ∧
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ hlow : ∀ (Q : ProjectedImmersionNeighborhood N U K δ) i,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress Q.1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
      let family := fun z : ProjectedImmersionNeighborhood N U K δ × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R (ProjectedStressFrame.projectedStress z.1.1)
          (frameOfImmersion hU z.1).2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair G (Euclidean 3) (groupCube D assign)),
        (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      ∀ Q : ProjectedImmersionNeighborhood N U K δ,
        EqOn (extendedProjectedStress p Q.1) (ProjectedStressFrame.projectedStress Q.1) (closedBall 0 (3 * r)) ∧
        let H := normalizedHomogeneousSymbol isOpen_univ (extendedProjectedStress p Q.1)
          (contDiff_affineFrameExtension p ((frameOfImmersion hU Q).2.1.mono (hpK.trans hKU))).contDiffOn;
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
            interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εw ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) := by
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx,
    ρ, εw, hρ, hρτ, hεw, centers, w, hlow₀, hclosure, hfreq, hprotect⟩ :=
    exists_constructed_signed_uniform_protection_with_graph_bounds hn hD T G assign hK hKU hball p hp0 hpK hr₀ hradius
  let hlow (F : ProjectedImmersionNeighborhood N U K δ) := hlow₀ (frameOfImmersion hU F)
  let family := fun z : ProjectedImmersionNeighborhood N U K δ × closedBall (0 : Euclidean n) r ↦
    currentGroup T assign R (ProjectedStressFrame.projectedStress z.1.1)
      (frameOfImmersion hU z.1).2.1 (hlow z.1) z.2
  let lift (z : ProjectedImmersionNeighborhood N U K δ × closedBall (0 : Euclidean n) r) :
      FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r :=
    (frameOfImmersion hU z.1, z.2)
  have hdir : directionSet family (groupCube D assign) ⊆
      directionSet (fun z : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R z.1.1 z.1.2.1 (hlow₀ z.1) z.2) (groupCube D assign) := by
    rintro v ⟨z, q, he⟩
    exact ⟨lift z, q, he⟩
  exact ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, ρ, εw, hρ, hρτ, hεw, centers, w, hlow,
    (closure_mono hdir).trans hclosure, fun z q ↦ hfreq (lift z) q,
    fun F ↦ by
      obtain ⟨heq, hrest⟩ := hprotect (frameOfImmersion hU F)
      refine ⟨heq, ?_⟩
      dsimp at hrest ⊢
      rcases hrest with ⟨hflow, ⟨charts, hderivative, hnorm, hcompact, hrestcharts⟩⟩
      refine ⟨hflow, ⟨charts, hderivative, hnorm, hcompact, ?_⟩⟩
      rcases hrestcharts with ⟨hzero, hsource, hbuffer, hsegment, hchain, hrect⟩
      exact ⟨hzero, hsource, hbuffer, hsegment, hchain, hrect⟩⟩

end JanetCartan.ProtectedFlow
