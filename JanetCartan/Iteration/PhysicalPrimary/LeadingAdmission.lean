module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Actual physical admission to the retained original leading callback

The arbitrary-current-map continuation retained by `PhysicalSeed` consumes
smoothness, immersion/rank, a fixed C14 budget, the two original geometric gaps,
and joint C6 frame closeness. Every one of those clauses is produced here for
the literal real Schwartz history. Constants precede the history and its scale.

The reference frame tolerance is the original source-normalization clause, not
an assumed current-frame estimate. No rows, Hamilton charts, scalar, source
scale, or original flow times are reselected. Consumer: the actual same-row
full/null-flow and `OriginalLeadingInputs.Solution` construction for
`main:prop:current-waves` and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary

open ProjectedStressFrame ActualCarriers.CurrentFullPhase

/-- Revised physical admissibility supplies ALL current-map hypotheses of
the original retained leading callback. The exact low budget is the prescribed
reference's C14 norm plus one, as in the original construction. The full joint
frame tolerance is proved from its componentwise source normalization with the
original order-six factor, never by changing the selected rows or flows. -/
theorem exists_history_leading_admission {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {η : ℝ} (hη : 0 < η)
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < (η / (2 * (6 + 1 : ℝ))) / 2) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ κ : ℝ, 0 < κ ∧
      ∃ A : ℕ → ℝ, (∀ q, 0 ≤ A q) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiff ℝ ∞ F ∧
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      cNorm (closedBall 0 r) 14 F ≤ cNorm (closedBall 0 r) 14 G.map + 1 ∧
      (∀ x ∈ closedBall 0 r, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ closedBall 0 r, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      cNorm (closedBall 0 r) 6 (projectedStress F - fun _ ↦ cubeStress n) < η ∧
      HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A := by
  obtain ⟨Sg, hSg, _C₀, _hC₀, κ, hκ, hgeom⟩ :=
    PhysicalGeometry.exists_cube_frame_neighborhood G hr hrR hR hB (by omega) horder
      (by positivity : 0 < η / (2 * (6 + 1 : ℝ))) hreference
  obtain ⟨St, _hSt, hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := embeddingDimension n) hB horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) r) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  refine ⟨max Sg St, hSg.trans (le_max_left _ _), κ, hκ, A, hA, ?_⟩
  intro R₀ hR₀ j u ell hu F
  have hRg := (le_max_left Sg St).trans hR₀
  have hRt := (le_max_right Sg St).trans hR₀
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _hC4, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRg j u ell hu
  have hK : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) := contDiffOn_pi.mpr hQ
  have hlow : cNorm (closedBall (0 : Euclidean n) r) 14 F ≤
      cNorm (closedBall (0 : Euclidean n) r) 14 G.map + 1 := by
    have hsmall := (cNorm_mono_order hStar (s := closedBall (0 : Euclidean n) r)
      (f := F - G.map)).trans_lt
      (hnear R₀ hRt (closedBall 0 r) G.map (isCompact_closedBall _ _) j u ell hu)
    have hadd := cNorm_add_le (isCompact_closedBall (0 : Euclidean n) r)
      (G.contDiff.of_le (by simp : (14 : ℕ∞ω) ≤ ∞))
      ((hF.sub G.contDiff).of_le (by simp : (14 : ℕ∞ω) ≤ ∞))
    have he : G.map + (F - G.map) = F := by abel
    change cNorm (closedBall (0 : Euclidean n) r) 14 (G.map + (F - G.map)) ≤
      cNorm (closedBall (0 : Euclidean n) r) 14 G.map +
        cNorm (closedBall (0 : Euclidean n) r) 14 (F - G.map) at hadd
    rw [he] at hadd
    linarith
  refine ⟨hF, hi, hrank, hlow, fun x hx ↦ hmet x (hK hx),
    fun x hx ↦ hnormal x (hK hx), ?_, hprofile R₀ (hSg.trans hRg) j u ell hu _ Subset.rfl⟩
  exact frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
    (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hK hx))).sub
      contDiffAt_const).of_le (by simp)) hη hclose

end JanetCartan.PhysicalPrimary
