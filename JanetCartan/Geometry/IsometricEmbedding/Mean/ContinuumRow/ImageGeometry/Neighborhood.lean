module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.JetFormula
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood

/-!
# Image coefficient bounds on the actual reference neighborhood

The producer of the physical coefficient inputs for `ContinuumRow.imageChannel`
in `app:ch_background:defn:bg-row`. The compact admissible range is derived from
the reference and primitive C8 map closeness. Smoothness and the reserve-two
one-high estimate for the actual coefficients are conclusions, not hypotheses.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.ProjectedStressFrame JanetCartan.GeometricProfile
open JanetCartan.CurrentGeometricNeighborhood

namespace JanetCartan.ContinuumRow.ImageGeometry

variable {n : ℕ}

/-- The actual reference and its C8 neighborhood have a common compact
admissible jet range (`app:ch_background:eq:bg-frame-tame`). The reference
may be source-scaled; no comparison to the unscaled cube jet is required. -/
theorem exists_image_coefficient_jet_neighborhood (G : FlatReference n)
    {R : ℝ} (hR : R < G.domain.chartRadius) :
    ∃ δ > 0, ∃ L : Set (StressJet n (embeddingDimension n)), IsCompact L ∧
      (∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) ∧
      ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
        cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
        Set.MapsTo (stressJet F) (Metric.closedBall 0 R) L := by
  obtain ⟨d, hd, L, hL, hu, hnear⟩ := exists_reference_jet_neighborhood G hR
  refine ⟨d / 2, half_pos hd, L, hL, hu, ?_⟩
  intro F hF hclose x hx
  apply hnear x hx
  have hb := norm_stressJet_sub_le (isCompact_closedBall (0 : Euclidean n) R)
    isOpen_univ (Set.subset_univ _) hF.contDiffOn G.contDiff.contDiffOn hx
  linarith

/-- All physical image coefficients are smooth, uniformly bounded at low
order, and satisfy the one-high bound with reserve two, solely from primitive
C8 closeness to the fixed actual reference (`app:ch_background:eq:bg-frame-tame`).
The cutoff-periodization construction consumes these estimates on the inner
closed ball; its support lies strictly inside this ball. All constants and the
neighborhood are chosen before the current map and every high order. -/
theorem exists_reference_reduced_coefficient_estimates (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius) :
    ∃ δ > 0, ∃ B > 0, ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
        cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
        ContDiffOn ℝ ∞ (geometricReducedCoefficients F) (Metric.ball 0 R) ∧
        cNorm (Metric.closedBall 0 r) 0 (geometricReducedCoefficients F) ≤ B ∧
        ∀ m, cNorm (Metric.closedBall 0 r) m (geometricReducedCoefficients F) ≤
          C m * (1 + cNorm (Metric.closedBall 0 R) (m + 2) F) := by
  obtain ⟨djet, hdjet, L, hL, hu, hjet⟩ := exists_image_coefficient_jet_neighborhood G hR
  obtain ⟨dgeo, hdgeo, M, hM, κ, _hκ, hgeo⟩ :=
    exists_geometric_neighborhood G hr hrR hR (by norm_num : (0 : ℝ) < 1)
  have hbounds := fun m ↦ exists_cNorm_ambientReducedCoefficients_comp_le
    (0 : Euclidean n) hr hL hu m
  choose C hC hbound using hbounds
  refine ⟨min djet dgeo, lt_min hdjet hdgeo, C 0 * (1 + M),
    mul_pos (hC 0) (by linarith), C, hC, ?_⟩
  intro F hF hclose
  have hFL := hjet F hF (hclose.trans_le (min_le_left _ _))
  obtain ⟨hi, hrank, hlow, _⟩ := hgeo Set.univ F isOpen_univ (Set.subset_univ _)
    hF.contDiffOn (hclose.trans_le (min_le_right _ _))
  have hball : Metric.closedBall (0 : Euclidean n) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have hclosed : Metric.closedBall (0 : Euclidean n) r ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall hrR.le
  have he (m : ℕ) : cNorm (Metric.closedBall 0 r) m (geometricReducedCoefficients F) =
      cNorm (Metric.closedBall 0 r) m (ambientReducedCoefficients ∘ stressJet F) :=
    cNorm_eq_of_eventuallyEq (fun x hx ↦
      (ambientReducedCoefficients_eventuallyEq hF Metric.isOpen_ball hi hrank
        (hball hx)).symm) m
  have hb (m : ℕ) : cNorm (Metric.closedBall 0 r) m (geometricReducedCoefficients F) ≤
      C m * (1 + cNorm (Metric.closedBall 0 r) (m + 2) F) := by
    rw [he m]
    exact hbound m F hF (fun x hx ↦ hFL (hclosed hx))
  refine ⟨contDiffOn_geometricReducedCoefficients hF Metric.isOpen_ball hi hrank, ?_, ?_⟩
  · exact (hb 0).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((cNorm_mono_order (by norm_num : 2 ≤ 4)).trans hlow)) (hC 0).le)
  · intro m
    exact (hb m).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (cNorm_mono_set_of_contDiffAt hclosed (isCompact_closedBall (0 : Euclidean n) R)
        (fun _ _ ↦ hF.contDiffAt.of_le (by simp)))) (hC m).le)

end JanetCartan.ContinuumRow.ImageGeometry
