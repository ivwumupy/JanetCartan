module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.ExtendedCover
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CompleteProduct

/-!
# Uniform protection with fixed weighted rectangles

The full-product geometric assembly for `app:ch_regular:thm:no-return`.
The same phases provide the invariant conic set and the uniform rectangles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover ActualCarriers ActualCarriers.FrozenPhaseReference
open FiniteChain.Retarded

/-- Complete-product protection and fixed four-weight rectangles for one
coefficient extension (`app:ch_regular:thm:no-return`). The compact sectors,
centers, widths and positive buffers precede the variable frame. Both
orientations and every finite chain are covered, including elliptic sources. -/
theorem exists_extended_frame_uniform_protection_with_graph_bounds {n : ℕ} (hn : 5 ≤ n)
    (p : BallExtension.Parameters (Euclidean n)) {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hbad : Disjoint Ω (cubeBadSubspaceUnion n)) :
    ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω ∧ (frozenSymbol n).h (0, ξ) = 0})
      (g : s → ComparisonGeometry (Euclidean n)) (r c C ε Lx : ℝ)
      (Γin Γout : Set (Euclidean n)),
      0 < r ∧ r < R ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧ 0 ≤ Lx ∧
      (∀ i : s, 3 * r < (g i).radius) ∧
      IsCompact Γin ∧ IsCompact Γout ∧ Γin ⊆ interior Γout ∧
      (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
      Γout ⊆ (cubeBadSubspaceUnion n)ᶜ ∧ Ω ⊆ interior Γin ∧
      ∀ τ : ℝ, 0 < τ → ∃ δ ρ εx : ℝ, 0 < δ ∧ 0 < ρ ∧ ρ < τ ∧ 0 < εx ∧
      ∃ (centers : (i : s) → Finset (CanonicalPhase (g i).tangentSpace))
        (w : (i : s) → (q : centers i) → CanonicalFactorWeights q.1 ρ),
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∃ charts : (i : s) → ComparisonChart H (g i),
          (∀ i : s, ∀ η ∈ (g i).parameters, ∀ x ∈ closedBall 0 (2 * r),
            ‖fderiv ℝ ((charts i).gradientMap η) x‖ ≤ Lx) ∧
          (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
            c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
              ‖ComparisonChart.familyGradient charts η x‖ ≤ C) ∧
          IsCompact (normalizedGraphImage (ComparisonChart.familyGradient charts)
            (closedBall 0 (2 * r)) univ) ∧
          let P := positiveConicLift (ComparisonChart.familyGradient charts)
            (ball 0 (2 * r)) univ;
          P ⊆ H.domain ∩ {z | H.h z = 0} ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω, H.h z = 0 → z ∈ P) ∧
          (∀ z ∈ P, closedBall (normalizedCovector z.2) ε ⊆
            interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ z ∈ P, ∀ w, CompleteCharacteristicSegment H (ball 0 (2 * r)) z w → w ∈ P) ∧
          (∀ z ∈ closedBall 0 r ×ˢ Ω, ∀ w k,
            PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k →
            closedBall (normalizedCovector w.2) ε ⊆
              interior Γin \ cubeBadSubspaceUnion n) ∧
          (∀ i : s, (charts i).canonicalSource r ⊆ ⋃ q ∈ centers i, ball q (ρ / 8)) ∧
          (∀ i : s, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
            canonicalFlowLift z ∈ (charts i).chart.source ∧
              closedBall (canonicalState (charts i).flow z).1 εx ⊆ ball 0 (2 * r)) ∧
          (∀ i : s, ∀ z ∈ (charts i).canonicalSource r, ∃ q : centers i,
            (w i q).base 0 z.1 * (w i q).frequency z.2 = 1 ∧
            (w i q).base 1 z.1 * (w i q).frequency z.2 = 1) := by
  obtain ⟨s, g, r, c, C, Lx, A, hr, hrR, hc, hC, hLx,
    hrad, hA, hAbad, hcover⟩ :=
    exists_extended_frame_uniform_cover_with_graph_bounds hn p hR hΩ hbad
  obtain ⟨Γin, Γout, ε, hε, hΓin, hΓout, hnest, hsymIn, hsymOut,
    hregular, hΩin, hΩbuffer, hAbuffer⟩ :=
    exists_regular_source_sectors hn hΩ hA hbad hAbad
  refine ⟨s, g, r, c, C, ε, Lx, Γin, Γout, hr, hrR, hc, hC, hε, hLx,
    hrad, hΓin, hΓout, hnest, hsymIn, hsymOut, hregular, hΩin, ?_⟩
  intro τ hτ
  obtain ⟨δ, ρ, εx, hδ, hρ, hρτ, hεx, centers, w, hcurrent⟩ := hcover τ hτ
  refine ⟨δ, ρ, εx, hδ, hρ, hρτ, hεx, centers, w, ?_⟩
  intro Q hQ hlow
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  obtain ⟨charts, hderivative, hb, hv, hrect, hbuffer, hweights⟩ := hcurrent Q hQ hlow
  have hrad' : ∀ i, r ≤ (g i).radius := fun i ↦ by linarith [hrad i]
  have hrad'' : ∀ i, 2 * r < (g i).radius := fun i ↦ by linarith [hrad i]
  have hsmooth : ContDiffOn ℝ ∞ H.h H.domain :=
    contDiffOn_normalizedSymbol isOpen_univ hE.contDiffOn
  let P := positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ
  have hsource : ∀ z ∈ closedBall 0 r ×ˢ Ω, H.h z = 0 → z ∈ P := by
    intro z hz hchar
    obtain ⟨η, he⟩ := hv z.1 hz.1 z.2 hz.2 hchar
    exact ⟨closedBall_subset_ball (by linarith) hz.1, η, mem_univ _,
      1, zero_lt_one, by simpa using he⟩
  have hPbuffer : ∀ z ∈ P, closedBall (normalizedCovector z.2) ε ⊆
      interior Γin \ cubeBadSubspaceUnion n := by
    rintro z ⟨hx, η, _, scale, hs, he⟩
    rw [he, normalizedCovector_smul_pos hs]
    exact hAbuffer _ (hb η z.1 (ball_subset_closedBall hx)).2.2
  refine ⟨charts, hderivative, fun η x hx ↦ ⟨(hb η x hx).1, (hb η x hx).2.1⟩, ?_,
    comparisonFamily_conicLift_zero_energy charts hrad', hsource, hPbuffer, ?_, ?_, hrect, hbuffer, hweights⟩
  · apply isCompact_normalizedGraphImage (isCompact_closedBall _ _)
      (ComparisonGeometry.isCompact_parameterFamily g)
      (ComparisonChart.continuousOn_familyGradient charts hrad')
    intro x hx η _
    exact norm_pos_iff.mp (hc.trans_le (hb η x hx).1)
  · intro z hz w hseg
    exact comparisonFamily_preserves_characteristicSegment rfl hsmooth charts hrad'' hz hseg
  · intro z hz w k hchain
    by_cases hchar : H.h z = 0
    · exact hPbuffer w (comparisonFamily_preserves_chain rfl hsmooth charts hrad''
        hchain (hsource z hz hchar))
    · rw [← elliptic_completeCharacteristic_chain_eq hchain hchar]
      exact hΩbuffer z.2 hz.2

end JanetCartan.ProtectedFlow
