module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalCover
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompleteSourcePlateau

/-!
# Complete-source plateau on the original protected terminal chains

Use the actual relative cover's larger compact as the finite solver compact.
Its original angular buffer lies in the unit plateau of the literal normalized
characteristic-plus-elliptic source. The compact and buffer precede every family,
reference, current map and chain length; all original source geometry remains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference
open GeometricProfile
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open FourierIntegral.LowBounds.FrequencyCutoff

/-- The original relative no-return producer supplies the terminal compact,
then the literal completed source on that compact supplies a unit plateau for
both signs of every complete and selected-factor chain. This retains all source
labels, limiting differences, graph bounds and reference margins on the same
cover and quantitative family (`app:ch_regular:thm:no-return`,
`app:ch_regular:lem:finite-chain`, `resolved-angular-tail`). -/
theorem exists_primitive_signed_complete_source_terminal_cover {d : ℕ} (hn : 5 ≤ d+1)
    {D : CoverData (d+1)} {c C : ℝ} (hD : D.IsValid c C)
    {b B : ℝ} (hbB : b < B)
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 B) isOpen_ball)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (hball : ∀ i, closedBall (0 : Euclidean (d+1)) (T i).data.localReference.stateRadius ⊆ closedBall 0 b)
    (p : BallExtension.Parameters (Euclidean (d+1))) (hp0 : p.center = 0)
    (hpb : p.radius ≤ b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hradius : ∀ i, r₀ < (T i).physicalRadius)
    (m : ℕ) (hm : 6 ≤ m) {εlow : ℝ} (hεlow : 0 < εlow) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ r δ a A ε τ εx : ℝ, 0 < r ∧ r < r₀ ∧ 3 * r < p.radius ∧
        0 < δ ∧ 0 < a ∧ 0 < A ∧ 0 < ε ∧ 0 < τ ∧ 0 < εx ∧
      ∃ Ω₀ Ω₁ Γin Γout : Set (Euclidean (d+1)),
        IsCompact Ω₀ ∧ IsCompact Ω₁ ∧ IsCompact Γin ∧ ∃ hΓout : IsCompact Γout,
        Ω₀ ⊆ interior Ω₁ ∧ Ω₁ ⊆ interior Γin ∧ Γin ⊆ interior Γout ∧
        (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
        (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
        (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
        Γout ⊆ (cubeBadSubspaceUnion (d+1))ᶜ ∧
        (0 : Euclidean (d+1)) ∉ Γout ∧
        (∀ ξ ∈ Γout, determinant (cubeStress (d+1)) ξ = 0 →
          fderiv ℝ (determinant (cubeStress (d+1))) ξ ≠ 0) ∧
      ∃ aperture > (0 : ℝ), (∀ ξ ∈ Γout, ∀ i, |ξ i| < aperture) ∧
      ∃ θ > (0 : ℝ),
        (∀ ξ ∈ Γin, closedBall ξ θ ⊆ interior Γout ∧
          closedBall (-ξ) θ ⊆ interior Γout) ∧
      ∃ (s : Finset {ξ : Euclidean (d+1) // ξ ∈ Ω₁ ∧ (frozenSymbol (d+1)).h (0, ξ) = 0})
        (g : s → ComparisonGeometry (Euclidean (d+1))),
        (∀ i : s, 3 * r < (g i).radius) ∧
      ∃ cgraph Cgraph Lx : ℝ, 0 < cgraph ∧ 0 < Cgraph ∧ 0 ≤ Lx ∧
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ ηref > (0 : ℝ), ∀ Gref : FlatReference (d+1), B < Gref.domain.chartRadius →
        (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) b) m
          (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i - cubeStress (d+1) i) < ηref) →
      ∃ Z₀ : Euclidean (d+1) → Fin (d+1) × Fin (d+1) → ℝ, ContDiff ℝ ∞ Z₀ ∧
      ∃ dmap > (0 : ℝ),
      ∃ lift : PrimitiveMapNeighborhood Gref B (m + 2) dmap →
        ProjectedImmersionNeighborhood (embeddingDimension (d+1)) (ball 0 B) (closedBall 0 b) δ,
      (∀ F, (lift F).1 = F.1) ∧
      ∃ hlow : ∀ (Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap) i,
        cNorm (closedBall (0 : Euclidean (d+1)) (T i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress (lift Q).1 - fun _ ↦ cubeStress (d+1)) < (T i).family.threshold,
      let family := fun z : PrimitiveMapNeighborhood Gref B (m + 2) dmap × closedBall (0 : Euclidean (d+1)) r ↦
        currentGroup T assign R (ProjectedStressFrame.projectedStress (lift z.1).1)
          (frameOfImmersion isOpen_ball (lift z.1)).2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair G (Euclidean 3) (groupCube D assign)),
        (∀ L ∈ cubeBadSubspaces (d+1), a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      (∀ (Dprofile : ℕ → ℝ) (order : ℕ), ∃ Cprofile : ℕ → ℝ,
        (∀ j, 0 < Cprofile j) ∧ ∀ slow : ℝ, 1 ≤ slow →
          ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
          HasDerivativeProfile (closedBall p.center p.radius)
            (geometricReducedCoefficients Q.1) order slow Dprofile →
          HasDerivativeProfile (closedBall (0 : Euclidean (d+1)) (3 * r))
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
          IsCompact (normalizedGraphImage (ComparisonChart.familyGradient charts)
            (closedBall 0 (2 * r)) univ) ∧
          let P := positiveConicLift (ComparisonChart.familyGradient charts)
            (ball 0 (2 * r)) univ;
          P ⊆ H.domain ∩ {z | H.h z = 0} ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, H.h z = 0 → z ∈ P) ∧
          (∀ z ∈ P, closedBall (normalizedCovector z.2) ε ⊆
            interior Γin \ cubeBadSubspaceUnion (d+1)) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            (closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion (d+1)) ∧
            (closedBall (normalizedCovector w.2) θ ⊆ interior Γout) ∧
            (closedBall (-normalizedCovector w.2) θ ⊆ interior Γout) ∧
              ∀ {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
                (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) Γout M),
                (closedBall (normalizedCovector w.2) θ ∪ closedBall (-normalizedCovector w.2) θ ⊆
                  interior {η | gammaTotal f hΓout η = 1}) ∧
                ∀ L > (0 : ℝ), ∀ ζ : Euclidean (d+1),
                  NormedSpace.normalize ζ ∈ closedBall (normalizedCovector w.2) θ ∪
                    closedBall (-normalizedCovector w.2) θ →
                  normalizedSourceMask f hΓout L ζ + physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1 ∧
                  (4*L ≤ ‖ζ‖ → normalizedSourceMask f hΓout L ζ = 1)) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εw ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ v k,
            PositiveConicChain (selectedFactorRelation charts w) z v k →
              (closedBall (normalizedCovector v.2) ε ⊆
                interior Γin \ cubeBadSubspaceUnion (d+1)) ∧
              (closedBall (normalizedCovector v.2) θ ⊆ interior Γout) ∧
              (closedBall (-normalizedCovector v.2) θ ⊆ interior Γout) ∧
              ∀ {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
                (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) Γout M),
                (closedBall (normalizedCovector v.2) θ ∪ closedBall (-normalizedCovector v.2) θ ⊆
                  interior {η | gammaTotal f hΓout η = 1}) ∧
                ∀ L > (0 : ℝ), ∀ ζ : Euclidean (d+1),
                  NormedSpace.normalize ζ ∈ closedBall (normalizedCovector v.2) θ ∪
                    closedBall (-normalizedCovector v.2) θ →
                  normalizedSourceMask f hΓout L ζ + physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1 ∧
                  (4*L ≤ ‖ζ‖ → normalizedSourceMask f hΓout L ζ = 1)) ∧
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
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx,
    hr, hrr₀, hrp, hδ, ha, hA, hε, hτ, hεx, hsectors⟩ :=
    exists_primitive_signed_terminal_cover_with_graph_bounds hn hD hbB T G assign
      hball p hp0 hpb hr₀ hradius m hm hεlow
  obtain ⟨Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, hzero, hregular,
    aperture, hAp, hApξ, θ, hθ, houter, hcharts⟩ := hsectors
  obtain ⟨s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, hweights⟩ := hcharts
  obtain ⟨ρ, εw, hρ, hρτ, hεw, centers, w, ηref, hηref, hproduce⟩ := hweights
  refine ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε,
    hτ, hεx, Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, hzero, hregular,
    aperture, hAp, hApξ, θ, hθ, houter, s, g, hgr,
    cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, ρ, εw, hρ, hρτ, hεw,
    centers, w, ηref, hηref, ?_⟩
  intro Gref hBref href
  obtain ⟨Z₀, hZ₀, dmap, hdmap, lift, hsame, hlow, hclosure, hfreq, hprofile, hcurrent⟩ :=
    hproduce Gref hBref href
  refine ⟨Z₀, hZ₀, dmap, hdmap, lift, hsame, hlow, hclosure, hfreq, hprofile, ?_⟩
  intro Q
  obtain ⟨hsmooth, hclose, heq, hprincipal, hop, hext, hflow, charts, hderiv,
    hnorm, hcompact, hzeroP, hsource, hbuffer, hsegment, hchain, hcover, hrect,
    hweights, hselected, helliptic, himage⟩ := hcurrent Q
  refine ⟨hsmooth, hclose, heq, hprincipal, hop, hext, hflow, charts, hderiv,
    hnorm, hcompact, hzeroP, hsource, hbuffer, hsegment, ?_, hcover, hrect,
    hweights, ?_, helliptic, himage⟩
  · intro z hz v k hsteps
    obtain ⟨ht, hp, hn⟩ := hchain z hz v k hsteps
    exact ⟨ht, hp, hn, fun f ↦ complete_source_plateau_on_outer_terminal_buffer
      hΓout hΓsymOut f (union_subset hp hn)⟩
  · intro z hz v k hsteps
    obtain ⟨ht, hp, hn⟩ := hselected z hz v k hsteps
    exact ⟨ht, hp, hn, fun f ↦ complete_source_plateau_on_outer_terminal_buffer
      hΓout hΓsymOut f (union_subset hp hn)⟩

end JanetCartan.ProtectedFlow
