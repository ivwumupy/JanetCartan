module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.SignedProtection
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.UniformProduct

/-!
# Fixed weighted factors for the complete signed carrier product

The labels, neighborhoods, finite comparison geometry, rectangle centers and
four weights are selected before the current frame in
`app:ch_regular:thm:no-return`. No source coverage is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open FrozenMenu ActualCarriers CurrentFullPhase ConstructedSignedGeometry SignedPairs
open HamiltonPhase PhaseCover FiniteChain.Retarded ActualCarriers.FrozenPhaseReference

/-- Uniform complete-source protection of the same radially labelled carriers
(`app:ch_regular:thm:no-return`). The closure contains all limiting short chords;
true beats are retained. All four weights and their complete doubled rectangles
are fixed before the frame, frequencies, histories and accuracy. -/
theorem exists_constructed_signed_uniform_protection {n : ℕ} (hn : 5 ≤ n)
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
      ∃ ρ εw : ℝ, 0 < ρ ∧ ρ < τ ∧ 0 < εw ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∃ hlow : ∀ (Q : FrameNeighborhood U K δ) i,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
      let family := fun z : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r ↦
        currentGroup T assign R z.1.1 z.1.2.1 (hlow z.1) z.2;
      closure (directionSet family (groupCube D assign)) ⊆ interior Ω₀ ∧
      (∀ z (q : Pair G (Euclidean 3) (groupCube D assign)),
        (∀ L ∈ cubeBadSubspaces n, a * q.beat ≤ ‖projectAway L (q.vector (family z))‖) ∧
        q.vector (family z) ≠ 0 ∧ ∀ lam : ℝ, 0 ≤ lam →
          a * (lam * q.beat) ≤ ‖lam • q.vector (family z)‖ ∧
          ‖lam • q.vector (family z)‖ ≤ A * (lam * q.beat)) ∧
      ∀ Q : FrameNeighborhood U K δ,
        EqOn (affineFrameExtension p Q.1) Q.1 (closedBall 0 (3 * r)) ∧
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q.1)
          (contDiff_affineFrameExtension p (Q.2.1.mono (hpK.trans hKU))).contDiffOn;
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
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εw ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) := by
  obtain ⟨R, hR, hinj, d, a, A, e, hd, ha, hA, _he, Ω₀, Ω₁, hΩ₀, hΩ₁,
    hΩnest, hΩsym₀, hΩsym₁, hΩann, hΩbad, _hΩbuffer, hlow₀, hclosure, hfreq⟩ :=
    exists_constructed_source_neighborhoods hn hD T G assign hK hKU hball hr₀ hradius
  have hcap : 0 < min r₀ (p.radius / 3) := lt_min hr₀ (div_pos p.radius_pos (by norm_num))
  obtain ⟨s, g, r, cl, cu, ε, Γin, Γout, hr, hrcap, _hcl, _hcu,
    hε, hgr, hΓin, hΓout, hΓnest, hΓsymIn, hΓsymOut, hΓbad, hΩΓ, hprotect⟩ :=
    exists_extended_frame_uniform_protection hn p hcap hΩ₁ hΩbad
  have hrr₀ : r < r₀ := hrcap.trans_le (min_le_left _ _)
  have hrp : 3 * r < p.radius := by
    have := hrcap.trans_le (min_le_right _ _)
    linarith
  obtain ⟨τ, df, εx, hτ, hdf, hεx, htubes⟩ :=
    exists_extended_frame_retained_flow_tubes p hr hΩ₁ (fun ξ hξ ↦
      norm_pos_iff.mp (lt_trans (by norm_num) (hΩann ξ hξ).1))
  obtain ⟨d', ρ, εw, hd', hρ, hρτ, hεw, centers, w, hcurrent⟩ := hprotect τ hτ
  let δ := min d (min d' df / 14)
  have hδ : 0 < δ := lt_min hd (div_pos (lt_min hd' hdf) (by norm_num))
  let promote (Q : FrameNeighborhood U K δ) : FrameNeighborhood U K d :=
    ⟨Q.1, Q.2.1, fun i ↦ (Q.2.2 i).trans_le (min_le_left _ _)⟩
  let hlow (Q : FrameNeighborhood U K δ) := hlow₀ (promote Q)
  let family := fun z : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r ↦
    currentGroup T assign R z.1.1 z.1.2.1 (hlow z.1) z.2
  let lift (z : FrameNeighborhood U K δ × closedBall (0 : Euclidean n) r) :
      FrameNeighborhood U K d × closedBall (0 : Euclidean n) r₀ :=
    (promote z.1, ⟨z.2.1, closedBall_subset_closedBall hrr₀.le z.2.2⟩)
  have hdir : directionSet family (groupCube D assign) ⊆
      directionSet (fun z : FrameNeighborhood U K d × closedBall (0 : Euclidean n) r₀ ↦
        currentGroup T assign R z.1.1 z.1.2.1 (hlow₀ z.1) z.2) (groupCube D assign) := by
    rintro v ⟨z, q, he⟩
    exact ⟨lift z, q, he⟩
  refine ⟨R, hR, hinj, r, δ, a, A, ε, τ, εx, hr, hrr₀, hrp, hδ, ha, hA, hε, hτ, hεx,
    Ω₀, Ω₁, Γin, Γout, hΩ₀, hΩ₁, hΓin, hΓout, hΩnest, hΩΓ, hΓnest,
    hΩsym₀, hΩsym₁, hΓsymIn, hΓsymOut, hΩann, hΓbad,
    s, g, hgr, ρ, εw, hρ, hρτ, hεw, centers, w, hlow, (closure_mono hdir).trans hclosure,
    fun z q ↦ hfreq (lift z) q, ?_⟩
  intro Q
  have hQ (x : Euclidean n) (hx : x ∈ closedBall p.center p.radius) :
      ContDiffAt ℝ ∞ Q.1 x := Q.2.1.contDiffAt (hU.mem_nhds (hKU (hpK hx)))
  have hs : ∀ x ∈ K, ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le
      (by simp)
  have hjoint : cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) < min d' df := by
    apply frame_cNorm_lt_of_componentwise hK hs (lt_min hd' hdf)
    intro i
    exact (Q.2.2 i).trans_le (by norm_num; exact min_le_right _ _)
  have hsmall : cNorm (closedBall p.center p.radius) 6
      (Q.1 - fun _ ↦ cubeStress n) < min d' df :=
    (cNorm_mono_set_of_contDiffAt hpK hK hs).trans_lt hjoint
  obtain ⟨charts, _hb, hcompact, hzero, hsource, hbuffer, hsegment, hchain,
    hrect, hphysical, hweights⟩ :=
    hcurrent Q.1 hQ (hsmall.trans_le (min_le_left _ _))
  refine ⟨?_, htubes Q.1 hQ (hsmall.trans_le (min_le_right _ _)),
    charts, hcompact, hzero, hsource, hbuffer, hsegment, hchain,
    hrect, hphysical, hweights⟩
  apply (affineFrameExtension_eqOn p Q.1).mono
  rw [hp0]
  exact closedBall_subset_closedBall hrp.le

end JanetCartan.ProtectedFlow
