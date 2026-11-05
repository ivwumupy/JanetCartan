module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.SignedProtection

/-!
# Protection for the literal projected frame of the current immersion

This specializes the common signed-source construction to the actual
`ProjectedStressFrame.projectedStress F`. Smoothness is derived from the
immersion and full normal rank. The remaining smallness assumption is exactly
the primitive componentwise frame neighborhood from the paper; no Hamilton,
signed-geometry or source-coverage premise is added.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference

/-- Primitive current immersions for `exists_projected_signed_protection`.
The componentwise projected-frame `C⁶` assumption is produced by the current
geometric neighborhood and its history specialization
(`app:ch_seed:setup:seed-current`, `app:ch_regular:thm:no-return`). -/
abbrev ProjectedImmersionNeighborhood {n : ℕ} (N : ℕ)
    (U K : Set (Euclidean n)) (δ : ℝ) :=
  {F : Euclidean n → Euclidean N // ContDiffOn ℝ ∞ F U ∧ IsImmersionOn F U ∧
    HasFullNormalRankOn F U ∧ ∀ i,
      cNorm K 6 (fun x ↦ ProjectedStressFrame.projectedStress F x i - cubeStress n i) < δ}

/-- The primitive current immersion supplies the smooth *literal* projected
frame required by the signed and protection constructions. No independent
frame is chosen (`app:ch_regular:thm:no-return`). -/
def frameOfImmersion {n N : ℕ} {U K : Set (Euclidean n)} {δ : ℝ}
    (hU : IsOpen U) (F : ProjectedImmersionNeighborhood N U K δ) :
    FrameNeighborhood U K δ :=
  ⟨ProjectedStressFrame.projectedStress F.1,
    contDiffOn_pi.mpr (fun i ↦ ProjectedStressFrame.contDiffOn_projectedStress hU
      F.2.1 F.2.2.1 F.2.2.2.1 i), F.2.2.2.2⟩

/-- The complete signed-source protection and retained-flow buffers for the
literal projected frame. The same fixed extension, radial labels and original
carrier charts are retained. Constants and neighborhoods precede the current
immersion and its higher norms; the closure includes limiting short chords.
For each current immersion, the finite retained rectangles, complete doubled
supports and all four smooth weights have one common canonical width.
Their source and target plateaus cover the whole compact source. Uniform rectangle selection over the current neighborhood remains open
(`app:ch_regular:thm:no-return`). -/
theorem exists_projected_signed_protection {n N : ℕ} (hn : 5 ≤ n)
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
          ∃ ρ > (0 : ℝ), ρ < τ ∧
            ∀ i : s, ∃ centers : Finset ((charts i).canonicalSource r),
              (charts i).canonicalSource r ⊆ ⋃ q ∈ centers, ball q.1 (ρ / 8) ∧
              (∀ q : (charts i).canonicalSource r, ∀ z ∈ closedBall q.1 (2 * ρ),
                canonicalFlowLift z ∈ (charts i).chart.source ∧
                  (canonicalState (charts i).flow z).1 ∈ ball 0 (2 * r)) ∧
              (∃ εx' > (0 : ℝ), ∀ q : (charts i).canonicalSource r,
                ∀ z ∈ closedBall q.1 (2 * ρ),
                  closedBall (canonicalState (charts i).flow z).1 εx' ⊆ ball 0 (2 * r)) ∧
              (∀ q ∈ centers, ∃ θ ν : (ℝ × (g i).tangentSpace) → ℝ,
                ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ ν ∧
                (∀ x, θ x ∈ Icc (0 : ℝ) 1) ∧ (∀ η, ν η ∈ Icc (0 : ℝ) 1) ∧
                HasCompactSupport θ ∧ HasCompactSupport ν ∧
                tsupport θ ⊆ ball q.1.1 (ρ / 2) ∧
                tsupport ν ⊆ ball q.1.2 (ρ / 2) ∧
                closedBall q.1.1 (ρ / 4) ⊆ interior {x | θ x = 1} ∧
                closedBall q.1.2 (ρ / 4) ⊆ interior {η | ν η = 1} ∧
                tsupport (fun z : CanonicalPhase (g i).tangentSpace ↦ θ z.1 * ν z.2) ⊆
                  closedBall q.1 (ρ / 2) ∧
                ∀ z ∈ closedBall q.1 (ρ / 4), θ z.1 * ν z.2 = 1) ∧
              (∃ w : (q : centers) → CanonicalFactorWeights q.1.1 ρ,
                ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers,
                  (w q).base 0 z.1 * (w q).frequency z.2 = 1 ∧
                  (w q).base 1 z.1 * (w q).frequency z.2 = 1) := by
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr,
    hlow₀, hclosure, hfreq, hprotect⟩ :=
    exists_constructed_signed_protection hn hD T G assign hK hKU hball p hp0 hpK hr₀ hradius
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
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, s, g, hgr, hlow,
    (closure_mono hdir).trans hclosure, fun z q ↦ hfreq (lift z) q,
    fun F ↦ by
      obtain ⟨heq, hrest⟩ := hprotect (frameOfImmersion hU F)
      refine ⟨heq, ?_⟩
      dsimp at hrest ⊢
      rcases hrest with ⟨hflow, ⟨charts, hcompact, hrestcharts⟩⟩
      refine ⟨hflow, ⟨charts, hcompact, ?_⟩⟩
      rcases hrestcharts with ⟨hzero, hsource, hbuffer, hsegment, hchain, hrect⟩
      exact ⟨hzero, hsource, hbuffer, hsegment, hchain, hrect⟩⟩

end JanetCartan.ProtectedFlow
