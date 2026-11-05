module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.HistoryCarrierBudget
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Closing the current-map inputs of the covering continuum row

The common normalized/history initializer retains a C8 neighborhood on the
original outer ball, even though the initialized reference's named chart is
smaller. Use that retained neighborhood on the SAME map. The actual admissible
prefix supplies its closeness, the complete fixed carrier budget, and the image
C8 input. Componentwise frame bounds give the joint frame bound with the
existing derivative-order factor. The consumer is
`LeadingCarrier.exists_covering_leading_density_row_before_geometry`.

Sources: `main:eq:displacement-budget`, `app:ch_background:defn:bg-row`, and
v2 `new:sec:order-of-choices`. The neighborhood premise below is the geometric
conclusion of `ReferenceInitialization.NormalizedHistory.
exists_common_normalized_history_reference`, instantiated at frame tolerance
`δframe / 14`. It is not an assumed current-map or operator bound.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow
open ProjectedStressFrame ActualCarriers.CurrentFullPhase CanonicalCarrier

/-- Discharge every current-map input of the covering row from the literal
admissible history and the SAME initialized C8 neighborhood. The frequency
threshold precedes every history and every image-chart radius. The fixed map
budget is exactly `2(n+1)+14`, including the full normal's PDO reserve
(`app:ch_background:defn:bg-row`, `main:eq:displacement-budget`). -/
theorem exists_initialScale_for_initialized_row_inputs {n : ℕ}
    (G : FlatReference n) {b R : ℝ} (hbR : b < R)
    {δgeom κ δframe δimage : ℝ}
    (hδgeom : 0 < δgeom) (hδframe : 0 < δframe) (hδimage : 0 < δimage)
    (hgeometry : ∀ (F : Euclidean n → Euclidean (embeddingDimension n)),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) 8 (F - G.map) < δgeom →
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      (∀ x ∈ ball 0 R, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      ∀ i, cNorm (closedBall 0 b) 6
        (fun x ↦ projectedStress F x i - cubeStress n i) < δframe / 14)
    {kMin : ℕ}
    (horder : displacementLoss n +
      bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ContDiff ℝ ∞ F ∧ IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      cNorm (closedBall 0 b) (canonicalCarrierLowOrder n) F ≤
        cNorm (closedBall 0 b) (canonicalCarrierLowOrder n) G.map + 1 ∧
      (∀ x ∈ closedBall 0 b, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ closedBall 0 b, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      cNorm (closedBall 0 b) 6 (projectedStress F - fun _ ↦ cubeStress n) < δframe ∧
      ∀ a : ℝ, cNorm (closedBall 0 (6 * a)) 8 (F - G.map) < δimage := by
  obtain ⟨S, hS, hinputs⟩ := exists_initialScale_for_row_map_inputs G.map G.contDiff
    (closedBall 0 b) (isCompact_closedBall _ _) horder (lt_min hδgeom hδimage)
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu
  obtain ⟨hF, hFM, hnear⟩ := hinputs R₀ hR₀ j u ell hu
  have hnearR : cNorm (closedBall 0 R) 8 (finiteHistoryMap G.map u - G.map) < δgeom := by
    have h := (hnear (R / 6)).trans_le (min_le_left _ _)
    convert h using 1
    congr 2
    ring
  obtain ⟨hi, hrank, hmet, hnormal, hclose⟩ := hgeometry _ hF hnearR
  have hBU : closedBall (0 : Euclidean n) b ⊆ ball 0 R := closedBall_subset_ball hbR
  have hframe : ContDiffOn ℝ ∞ (projectedStress (finiteHistoryMap G.map u)) (ball 0 R) :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF.contDiffOn hi hrank)
  refine ⟨hF, hi, hrank, hFM, fun x hx ↦ hmet x (hBU hx),
    fun x hx ↦ hnormal x (hBU hx), ?_, fun a ↦ (hnear a).trans_le (min_le_right _ _)⟩
  apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
    (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hBU hx))).sub
      contDiffAt_const).of_le (by simp)) hδframe
  simpa only [Pi.sub_apply, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    show (2 : ℝ) * (6 + 1) = 14 by norm_num] using hclose

end JanetCartan.ContinuumRow
