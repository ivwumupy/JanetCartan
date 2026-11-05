module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalGeometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.PrimitiveProtection

/-!
# The actual outer angular cover of the original signed terminal chains

Apply the relative primitive producer to the supplied cover, full source family,
assignment and extension. Its original sectors, source coverage, graph bounds,
comparison charts, complete chains and reference admission remain attached to
one witness. The outer sector `Γout` is the compact for the complete source:
it contains uniform positive neighborhoods of BOTH terminal orientations.
All cover and buffer choices precede the reference and current map.
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

/-- Construct the complete terminal angular cover from the original relative
signed no-return producer. `Γout` supplies the larger source plateau, while
`Γin` contains the original terminal buffers. The added positive collar is
uniform over source labels, conic scales, current maps and chain lengths.
The original selected relations already include both orientations and elliptic
identity steps. No reference, menu or source family is reselected
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_primitive_signed_terminal_cover_with_graph_bounds {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {b B : ℝ} (hbB : b < B)
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 B) isOpen_ball)
    (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ closedBall 0 b)
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    (hpb : p.radius ≤ b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hradius : ∀ i, r₀ < (T i).physicalRadius)
    (m : ℕ) (hm : 6 ≤ m) {εlow : ℝ} (hεlow : 0 < εlow) :
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
        (0 : Euclidean n) ∉ Γout ∧
        (∀ ξ ∈ Γout, determinant (cubeStress n) ξ = 0 →
          fderiv ℝ (determinant (cubeStress n)) ξ ≠ 0) ∧
      ∃ aperture > (0 : ℝ), (∀ ξ ∈ Γout, ∀ i, |ξ i| < aperture) ∧
      ∃ θ > (0 : ℝ),
        (∀ ξ ∈ Γin, closedBall ξ θ ⊆ interior Γout ∧
          closedBall (-ξ) θ ⊆ interior Γout) ∧
      ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω₁ ∧ (frozenSymbol n).h (0, ξ) = 0})
        (g : s → ComparisonGeometry (Euclidean n)),
        (∀ i : s, 3 * r < (g i).radius) ∧
      ∃ cgraph Cgraph Lx : ℝ, 0 < cgraph ∧ 0 < Cgraph ∧ 0 ≤ Lx ∧
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ ηref > (0 : ℝ), ∀ Gref : FlatReference n, B < Gref.domain.chartRadius →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) m
          (fun x ↦ ProjectedStressFrame.projectedStress Gref.map x i - cubeStress n i) < ηref) →
      ∃ Z₀ : Euclidean n → Fin n × Fin n → ℝ, ContDiff ℝ ∞ Z₀ ∧
      ∃ dmap > (0 : ℝ),
      ∃ lift : PrimitiveMapNeighborhood Gref B (m + 2) dmap →
        ProjectedImmersionNeighborhood (embeddingDimension n) (ball 0 B) (closedBall 0 b) δ,
      (∀ F, (lift F).1 = F.1) ∧
      ∃ hlow : ∀ (Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap) i,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress (lift Q).1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
      let family := fun z : PrimitiveMapNeighborhood Gref B (m + 2) dmap × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R (ProjectedStressFrame.projectedStress (lift z.1).1)
          (frameOfImmersion isOpen_ball (lift z.1)).2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair G (Euclidean 3) (groupCube D assign)),
        (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      (∀ (Dprofile : ℕ → ℝ) (order : ℕ), ∃ Cprofile : ℕ → ℝ,
        (∀ j, 0 < Cprofile j) ∧ ∀ slow : ℝ, 1 ≤ slow →
          ∀ Q : PrimitiveMapNeighborhood Gref B (m + 2) dmap,
          HasDerivativeProfile (closedBall p.center p.radius)
            (geometricReducedCoefficients Q.1) order slow Dprofile →
          HasDerivativeProfile (closedBall (0 : Euclidean n) (3 * r))
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
            interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω₁, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            (closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion n) ∧
            (closedBall (normalizedCovector w.2) θ ⊆ interior Γout) ∧
            (closedBall (-normalizedCovector w.2) θ ⊆ interior Γout)) ∧
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
                interior Γin \ cubeBadSubspaceUnion n) ∧
              (closedBall (normalizedCovector v.2) θ ⊆ interior Γout) ∧
              (closedBall (-normalizedCovector v.2) θ ⊆ interior Γout)) ∧
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
  have hgeometry :=
    exists_primitive_signed_no_return_with_graph_bounds hn hD hbB T G assign
      hball p hp0 hpb hr₀ hradius m hm hεlow
  obtain ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx,
    hr, hrr₀, hrp, hδ, ha, hA, hε, hτ, hεx, hsectors⟩ := hgeometry
  obtain ⟨Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad, hcharts⟩ := hsectors
  obtain ⟨s, g, hgr, cgraph, Cgraph, Lx, hcgraph, hCgraph, hLx, hweights⟩ := hcharts
  obtain ⟨ρ, εw, hρ, hρτ, hεw, centers, w, ηref, hηref, hproduce⟩ := hweights
  obtain ⟨hzero, hregular, aperture, hAp, hApξ, θ, hθ, houter⟩ :=
    protected_terminal_compact_selection_data hn hΓin hΓout hΓnest hΓsymOut hΓbad
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
    have ht := hchain z hz v k hsteps
    exact ⟨ht, houter _ (interior_subset (ht (mem_closedBall_self hε.le)).1)⟩
  · intro z hz v k hsteps
    have ht := hselected z hz v k hsteps
    exact ⟨ht, houter _ (interior_subset (ht (mem_closedBall_self hε.le)).1)⟩

end JanetCartan.ProtectedFlow
