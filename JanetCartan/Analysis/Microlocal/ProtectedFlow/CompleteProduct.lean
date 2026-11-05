module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.RegularSectors
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ComparisonPropagation

/-!
# Uniform protection for the whole extended-frame source product

This assembles the actual phase cover, fixed regular sectors and conic
propagation for `app:ch_regular:thm:no-return`. The source coverage, graph
regularity and invariance are conclusions derived from primitive frame
closeness. The same buffer works for all conic scales, orientations and finite
chain lengths. Actual finite-factor rectangles are a separate construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover ActualCarriers ActualCarriers.FrozenPhaseReference

/-- The constructed positive conic family lies in the actual characteristic
set on its entire physical region (`app:ch_regular:defn:protected-saturation`). -/
theorem comparisonFamily_conicLift_zero_energy {n : ℕ} {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)} {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart H (g i)) {r : ℝ}
    (hradius : ∀ i, r ≤ (g i).radius) :
    positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ ⊆
      H.domain ∩ {z | H.h z = 0} := by
  rintro z ⟨hx, η, _, scale, hs, he⟩
  have hz := ComparisonChart.zero_energy_familyGradient C hradius η
    (ball_subset_closedBall hx)
  have hm := (C η.1).homogeneous.scale_mem _ hz.1 scale hs
  have hzero := (C η.1).homogeneous.scale_symbol _ hz.1 scale hs
  rw [hz.2, mul_zero] at hzero
  change (z.1, z.2) ∈ H.domain ∧ H.h (z.1, z.2) = 0
  rw [he]
  exact ⟨hm, hzero⟩

/-- From primitive frame closeness, construct fixed sectors, a common physical
ball, and actual comparison charts protecting the entire compact source
product. The conic family is characteristic and invariant under every complete
segment; all finite chains from the source have one positive angular buffer.
Elliptic points are included via their proved identity behavior. Geometry and
buffers precede the current frame (`app:ch_regular:thm:no-return`). -/
theorem exists_extended_frame_protection {n : ℕ} (hn : 5 ≤ n)
    (p : BallExtension.Parameters (Euclidean n)) {R : ℝ} (hR : 0 < R)
    {Ω : Set (Euclidean n)} (hΩ : IsCompact Ω)
    (hbad : Disjoint Ω (cubeBadSubspaceUnion n)) :
    ∃ (s : Finset {ξ : Euclidean n // ξ ∈ Ω ∧ (frozenSymbol n).h (0, ξ) = 0})
      (g : s → ComparisonGeometry (Euclidean n)) (r δ c C ε : ℝ)
      (Γin Γout : Set (Euclidean n)),
      0 < r ∧ r < R ∧ 0 < δ ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      (∀ i : s, 3 * r < (g i).radius) ∧
      IsCompact Γin ∧ IsCompact Γout ∧ Γin ⊆ interior Γout ∧
      (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
      Γout ⊆ (cubeBadSubspaceUnion n)ᶜ ∧ Ω ⊆ interior Γin ∧
      ∀ (Q : Euclidean n → Fin n → MetricTensor n)
        (hQ : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x),
        cNorm (closedBall p.center p.radius) 6 (Q - fun _ ↦ cubeStress n) < δ →
        let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q)
          (contDiff_affineFrameExtension p
            (fun x hx ↦ (hQ x hx).contDiffWithinAt)).contDiffOn;
        ∃ charts : (i : s) → ComparisonChart H (g i),
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
              interior Γin \ cubeBadSubspaceUnion n) := by
  obtain ⟨s, g, r, δ, c, C, e, A, hr, hrR, hδ, hc, hC, _he,
    hrad, hA, hAbad, _hAbuffer, hcover⟩ :=
    exists_extended_frame_comparison_cover hn p hR hΩ hbad
  obtain ⟨Γin, Γout, ε, hε, hΓin, hΓout, hnest, hsymIn, hsymOut,
    hregular, hΩin, hΩbuffer, hAbuffer⟩ :=
    exists_regular_source_sectors hn hΩ hA hbad hAbad
  refine ⟨s, g, r, δ, c, C, ε, Γin, Γout, hr, hrR, hδ, hc, hC, hε,
    hrad, hΓin, hΓout, hnest, hsymIn, hsymOut, hregular, hΩin, ?_⟩
  intro Q hQ hlow
  let hE := contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt)
  let H := normalizedHomogeneousSymbol isOpen_univ (affineFrameExtension p Q) hE.contDiffOn
  obtain ⟨charts, hb, hv⟩ := hcover Q hQ hlow
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
  refine ⟨charts, fun η x hx ↦ ⟨(hb η x hx).1, (hb η x hx).2.1⟩, ?_,
    comparisonFamily_conicLift_zero_energy charts hrad', hsource, hPbuffer, ?_, ?_⟩
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
