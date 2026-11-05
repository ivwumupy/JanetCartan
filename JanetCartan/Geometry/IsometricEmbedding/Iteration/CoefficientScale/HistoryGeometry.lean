module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FiniteHistoryBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Step.History

/-!
# Fixed geometric bounds for actual admissible histories

The geometric part of `main:prop:current-scale` follows from the prospective
displacement budget `main:eq:displacement-budget` for the literal
`finiteHistoryMap G.map u`. We control C8 displacement on the outer closed ball,
obtain the metric and normal gaps on the open working ball, and measure the low
map and frame norms on the strictly smaller closed ball.

The reference and its source scale remain fixed. All constants and the initial
scale threshold precede the initial scale, stage, history, and any later target
or accuracy parameters. Admissibility supplies both the exact band/L² budgets
and smoothness; no geometric property of the current map is assumed.

The cube-frame conclusion of `app:ch_seed:setup:seed-current` additionally uses
the fixed reference's C6 cube-frame tolerance. The parent constructions in
`Iteration/CoefficientScale` and the uniform history step must instantiate that
reference invariant from `Reference/Initialization/ScaledReference` and supply
the admissible prefix. These results do not construct corrections or prove the
full coefficient profiles or `UniformHistoryCorrection`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.ProjectedStressFrame

namespace JanetCartan.HistoryGeometry

/-- `main:eq:displacement-budget`: one threshold controls the C8 displacement of
every actual admissible prefix on the outer closed ball. This supplies the
closeness input of both geometric persistence theorems below. The finite-history
map and scale are definitionally the ones in `FiniteHistoryBounds`; in particular
the support constant two and the extra power one in the L² budget are unchanged. -/
theorem exists_initialScale_for_c8_neighborhood {n N : ℕ}
    (G : Euclidean n → Euclidean N) (R : ℝ) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
        cNorm (Metric.closedBall 0 R) 8 (finiteHistoryMap G u - G) < δ := by
  obtain ⟨T, hT, hnear⟩ :=
    FiniteHistoryBounds.exists_initialScale_for_prefix_neighborhood
      (F := Euclidean N) 8 horder hδ
  refine ⟨T, hT, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hclose := hnear R₀ hR₀ (Metric.closedBall 0 R) G j u
    (fun i ↦ (ell i : ℝ)) (isCompact_closedBall _ _)
    (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1)
    (fun i ↦ (hu i).2.2.2) (fun i ↦ Nat.cast_le.mpr (hu i).1)
  exact hclose.trans (half_lt_self hδ)

/-- The geometric first component of `main:prop:current-scale`, uniformly over
every literal admissible history, using `main:eq:displacement-budget` on the
outer closed ball. The metric energy gap is one quarter; the separate positive
normal gap acts on each current map's own normal spaces. The threshold and all
bounds are chosen before the initial scale, stage, and prefix. -/
theorem exists_geometric_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 2 ≤ T ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
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
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_c8_neighborhood G.map R horder hδ
  refine ⟨T, hT, C₀, hC₀, κ, hκ, ?_⟩
  intro R₀ hR₀ j u ell hu
  exact hgeometry Set.univ (finiteHistoryMap G.map u) isOpen_univ
    (Set.subset_univ _) (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
    (hnear R₀ hR₀ j u ell hu)

/-- `app:ch_seed:setup:seed-current` for every actual admissible prefix, with
the original reference and its source scale fixed. Only the reference C6
cube-frame tolerance is additional to the fixed data and the prospective
history budgets. Its producer is `exists_scaled_flatReference` (or
`exists_scaled_reference_iteration_inputs`) with tolerance `ε / 2`, restricted
to this inner closed ball using the producer's smooth neighborhood. The current
cube-frame bound, smoothness, rank, and both gaps are conclusions. -/
theorem exists_cube_frame_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin)
    {ε : ℝ} (hε : 0 < ε)
    (hreference : ∀ i, cNorm (Metric.closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε / 2) :
    ∃ T : ℝ, 2 ≤ T ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∀ R₀, T ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
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
  obtain ⟨T, hT, hnear⟩ := exists_initialScale_for_c8_neighborhood G.map R horder hδ
  refine ⟨T, hT, C₀, hC₀, κ, hκ, ?_⟩
  intro R₀ hR₀ j u ell hu
  exact hgeometry Set.univ (finiteHistoryMap G.map u) isOpen_univ
    (Set.subset_univ _) (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
    (hnear R₀ hR₀ j u ell hu)

end JanetCartan.HistoryGeometry
