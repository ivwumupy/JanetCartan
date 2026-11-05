module

public import JanetCartan.Iteration.PhysicalHistory
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood

/-!
# The same-reference geometric neighborhood for physical histories

For `main:prop:current-scale` and `app:ch_seed:setup:seed-current` in
`paper-v2.tex`, apply the actual physical history estimates to the generic
geometric persistence theorem.  The prescribed reference, its source dilation,
and the actual map `RevisedGlobal.finiteMap G.map u` never change.  No periodic
representative, geometric success assumption, or new initializer is used.

The consumers are the original-data producer of
`RevisedGlobal.UniformHistoryCorrection` and the same-current-field regular
sector and retained-response coefficient estimates.  This file constructs
geometric inputs, not the wave/mean/pair correction itself.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.ProjectedStressFrame

namespace JanetCartan.PhysicalGeometry

/-- `main:eq:displacement-budget`: a single initial-scale threshold gives the
actual C8 neighborhood of the same prescribed map for every physical prefix.
The threshold precedes the scale, length, increments and accuracy orders. -/
theorem exists_initialScale_for_c8_neighborhood {n N : ℕ}
    (G : Euclidean n → Euclidean N) (R : ℝ) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ),
      RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        cNorm (Metric.closedBall 0 R) 8 (RevisedGlobal.finiteMap G u - G) < δ := by
  obtain ⟨T, hT, hnear⟩ := PhysicalHistory.exists_initialScale_for_prefix_neighborhood
    (N := N) hB horder hδ
  refine ⟨T, hT, ?_⟩
  intro R₀ hR₀ j u ell hu
  exact (cNorm_mono_order hStar).trans_lt
    ((hnear R₀ hR₀ (Metric.closedBall 0 R) G (isCompact_closedBall _ _) j u ell hu).trans
      (half_lt_self hδ))

/-- `main:prop:current-scale`: actual physical admissibility produces immersion,
full normal rank, the metric energy gap, a gap on each current normal space,
and projected-frame closeness.  The reference and the current map are fixed
literally, and all constants precede every history and target parameter. -/
theorem exists_geometric_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 2 ≤ T ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
      cNorm (Metric.closedBall 0 r) 4 F ≤ C₀ ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (Metric.ball 0 R)) ∧
      ∀ i, cNorm (Metric.closedBall 0 r) 6
        (fun x ↦ projectedStress F x i - projectedStress G.map x i) < η := by
  obtain ⟨δ, hδ, C₀, hC₀, κ, hκ, hgeometry⟩ :=
    CurrentGeometricNeighborhood.exists_geometric_neighborhood G hr hrR hR hη
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_c8_neighborhood
    G.map R hB hStar horder hδ
  refine ⟨T, hT, C₀, hC₀, κ, hκ, ?_⟩
  intro R₀ hR₀ j u ell hu
  exact hgeometry Set.univ (RevisedGlobal.finiteMap G.map u) isOpen_univ
    (Set.subset_univ _) (RevisedGlobal.contDiffOn_finiteMap G.contDiff.contDiffOn u)
    (hnear R₀ hR₀ j u ell hu)

/-- `app:ch_seed:setup:seed-current`: the same physical histories remain in the
cube-frame class of the prescribed scaled reference.  Only the fixed reference
cube tolerance is an input; current-frame success is produced from admissibility.
The reference-tolerance producer is the already selected scaled initializer. -/
theorem exists_cube_frame_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {ε : ℝ} (hε : 0 < ε)
    (hreference : ∀ i, cNorm (Metric.closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε / 2) :
    ∃ T : ℝ, 2 ≤ T ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
      cNorm (Metric.closedBall 0 r) 4 F ≤ C₀ ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (Metric.ball 0 R)) ∧
      ∀ i, cNorm (Metric.closedBall 0 r) 6
        (fun x ↦ projectedStress F x i - cubeStress n i) < ε := by
  obtain ⟨δ, hδ, C₀, hC₀, κ, hκ, hgeometry⟩ :=
    CurrentGeometricNeighborhood.exists_cube_frame_neighborhood G hr hrR hR hε hreference
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_c8_neighborhood
    G.map R hB hStar horder hδ
  refine ⟨T, hT, C₀, hC₀, κ, hκ, ?_⟩
  intro R₀ hR₀ j u ell hu
  exact hgeometry Set.univ (RevisedGlobal.finiteMap G.map u) isOpen_univ
    (Set.subset_univ _) (RevisedGlobal.contDiffOn_finiteMap G.contDiff.contDiffOn u)
    (hnear R₀ hR₀ j u ell hu)

/-- `main:prop:current-scale`: the second jets of every actual physical prefix
lie in one compact subset of both geometric unit loci.  This is derived from
the fixed reference and genuine C8 displacement, not assumed of the histories. -/
theorem exists_history_jet_range {n : ℕ} (G : FlatReference n)
    {R : ℝ} (hR : R < G.domain.chartRadius) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ L : Set (StressJet n (embeddingDimension n)), IsCompact L ∧
      (∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) ∧
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        Set.MapsTo (stressJet (RevisedGlobal.finiteMap G.map u)) (Metric.closedBall 0 R) L := by
  obtain ⟨d, hd, L, hL, hunit, hnear⟩ :=
    CurrentGeometricNeighborhood.exists_reference_jet_neighborhood G hR
  obtain ⟨S, hS, hclose⟩ := exists_initialScale_for_c8_neighborhood
    G.map R hB hStar horder (half_pos hd)
  refine ⟨L, hL, hunit, S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu x hx
  apply hnear x hx
  have hb := CurrentGeometricNeighborhood.norm_stressJet_sub_le
    (isCompact_closedBall (0 : Euclidean n) R) isOpen_univ (Set.subset_univ _)
    (RevisedGlobal.contDiffOn_finiteMap G.contDiff.contDiffOn u) G.contDiff.contDiffOn hx
  have hc := hclose R₀ hR₀ j u ell hu
  exact hb.trans (by linarith)

end JanetCartan.PhysicalGeometry
