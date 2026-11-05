module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Measured
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.StressPrimitives

/-!
# Projected-stress and measured residual on the original source chart

Obtain the reference and current projected-frame smoothness, both gaps and
the finite-order frame difference from the fixed immersion neighborhood, then
use the exact measured residual. This reduces the low/high datum estimates to
only the geometric immersion and the original physical mean difference; the
latter is the retained finite mean producer, not a whole residual assumption
(`app:ch_background:prop:bg-current`, `app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalInverseContinuity
open ProjectedStressFrame ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ContinuumRow PositiveBackground PhysicalBackground

/-- The literal projected stress is smooth on the original four-radius chart
and close on the closed measurement support. Only `max 8 (s+2)` physical
jets are needed; both inverse nondegeneracy bounds are produced here. -/
theorem exists_measured_projectedStress_tolerance {n : ℕ} (G : FlatReference n) {r : ℝ}
    (hr : 0 < r) (hR : 6 * r < G.domain.chartRadius) (s : ℕ) {η : ℝ} (hη : 0 < η) :
    ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 (4 * r)) ∧
    ∃ δ > 0, ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
      cNorm (closedBall 0 (6 * r)) (max 8 (s + 2)) (F - G.map) < δ →
      ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (4 * r)) ∧
      cNorm (closedBall 0 (3 * r)) s (projectedStress F - projectedStress G.map) < η := by
  let W := ball (0 : Euclidean n) (4 * r)
  let K := closedBall (0 : Euclidean n) (3 * r)
  have hW : IsOpen W := isOpen_ball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKW : K ⊆ W := closedBall_subset_ball (by linarith)
  have hWB : W ⊆ ball (0 : Euclidean n) (6 * r) := ball_subset_ball (by linarith)
  have hKB := hKW.trans hWB
  have hnorm (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F) :
      cNorm K 4 F ≤ cNorm (closedBall 0 (4 * r)) 4 F :=
    cNorm_mono_set_of_contDiffAt (hKW.trans ball_subset_closedBall) (isCompact_closedBall _ _)
      (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
  obtain ⟨d, hd, C, _, κ, hκ, hgeo⟩ := CurrentGeometricNeighborhood.exists_geometric_neighborhood
    G (show 0 < 4 * r by positivity) (show 4 * r < 6 * r by linarith) hR (by norm_num : (0 : ℝ) < 1)
  have hG := hgeo univ G.map isOpen_univ (subset_univ _) G.contDiff.contDiffOn
    (by simpa only [sub_self, cNorm_zero] using hd)
  have hiG : IsImmersionOn G.map W := fun x hx ↦ hG.1 x (hWB hx)
  have hrG : HasFullNormalRankOn G.map W := fun x hx ↦ hG.2.1 x (hWB hx)
  obtain ⟨dQ, hdQ, hcompare⟩ := exists_projectedStress_sub_tolerance hK hW hKW G.contDiff.contDiffOn
    hiG (C₀ := C) (κmet := 1 / 4) (κnormal := κ) (by norm_num) hκ
    ((hnorm _ G.contDiff).trans hG.2.2.1) (fun x hx ↦ hG.2.2.2.1 x (hKB hx))
    (fun x hx ↦ hG.2.2.2.2.1 x (hKB hx)) s hη
  refine ⟨contDiffOn_pi.mpr (contDiffOn_projectedStress hW G.contDiff.contDiffOn hiG hrG),
    min d dQ, lt_min hd hdQ, ?_⟩
  intro F hF hsmall
  have hf := hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn
    ((cNorm_mono_order (le_max_left 8 (s + 2))).trans_lt (hsmall.trans_le (min_le_left _ _)))
  have hiF : IsImmersionOn F W := fun x hx ↦ hf.1 x (hWB hx)
  have hrF : HasFullNormalRankOn F W := fun x hx ↦ hf.2.1 x (hWB hx)
  have hset := cNorm_mono_set_of_contDiffAt (hKB.trans ball_subset_closedBall)
    (isCompact_closedBall _ _) (fun _ _ ↦ (hF.sub G.contDiff).contDiffAt.of_le
      (show ((s + 2 : ℕ) : ℕ∞ω) ≤ ∞ by simp))
  have hnear := hset.trans_lt ((cNorm_mono_order (le_max_right 8 (s + 2))).trans_lt
    (hsmall.trans_le (min_le_right _ _)))
  exact ⟨contDiffOn_pi.mpr (contDiffOn_projectedStress hW hF.contDiffOn hiF hrF),
    hcompare F hF.contDiffOn hiF ((hnorm F hF).trans hf.2.2.1)
      (fun x hx ↦ hf.2.2.2.1 x (hKB hx)) (fun x hx ↦ hf.2.2.2.2.1 x (hKB hx)) hnear⟩

/-- Literal measured-source transfer with no smoothness or difference premise
on the moving projected stress. The geometric mean comparison on the retained
support and the immersion jet neighborhood suffice both for arbitrarily small
base error and the fixed high cap `S_s e₀ + 1`. -/
theorem exists_measured_source_tolerance_of_mean_jet {n : ℕ} (G : FlatReference n) {r : ℝ}
    (hr : 0 < r) (hcell : 4 * r < 1 / 2) (hR : 6 * r < G.domain.chartRadius)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀)
    (H₀ : MetricField n) (hH₀ : ContDiffOn ℝ ∞ H₀ (ball 0 (4 * r))) (s : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ hQ₀ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 (4 * r)),
    let e₀ := measuredSourceToL2 hr hcell (projectedStress G.map)
      (linearizedMetric G.map (tangentVariation G.map X₀) + H₀) hQ₀ (tangentMean_smoothOn G.contDiff hX₀ hH₀)
    let S := periodicSobolevScale n (Euclidean n)
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F),
      cNorm (closedBall 0 (6 * r)) (max 8 (s + 2)) (F - G.map) < δ →
    ∃ hQ : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (4 * r)),
    ∀ (H : MetricField n) (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r))),
      cNorm (closedBall 0 (3 * r)) s (H - H₀) < δ →
      let e := measuredSourceToL2 hr hcell (projectedStress F)
        (linearizedMetric F (tangentVariation F X₀) + H) hQ (tangentMean_smoothOn hF hX₀ hH)
      e ∈ S.level s ∧ ‖e - e₀‖ ≤ η ∧ S.gradeNorm s e ≤ S.gradeNorm s e₀ + 1 := by
  have hQ₀ := (exists_measured_projectedStress_tolerance G hr hR s hη).1
  refine ⟨hQ₀, ?_⟩
  intro e₀ S
  obtain ⟨d, hd, hsource⟩ := exists_measured_tangent_source_tolerance hr hcell X₀ hX₀ G.map
    G.contDiff hQ₀ H₀ hH₀ s hη
  have hd3 : 0 < d / 3 := by positivity
  obtain ⟨dq, hdq, hQ⟩ := (exists_measured_projectedStress_tolerance G hr hR s hd3).2
  refine ⟨min (d / 3) dq, lt_min hd3 hdq, ?_⟩
  intro F hF hsmall
  obtain ⟨hQF, hQdiff⟩ := hQ F hF (hsmall.trans_le (min_le_right _ _))
  refine ⟨hQF, ?_⟩
  intro H hH hmean
  have hdom := cNorm_mono_set_of_contDiffAt
    (closedBall_subset_closedBall (by linarith : 3 * r ≤ 6 * r))
    (isCompact_closedBall (0 : Euclidean n) (6 * r))
    (fun _ _ ↦ (hF.sub G.contDiff).contDiffAt.of_le (show ((s + 2 : ℕ) : ℕ∞ω) ≤ ∞ by simp))
  have hFdiff : cNorm (closedBall 0 (3 * r)) (s + 2) (F - G.map) < d / 3 :=
    hdom.trans_lt ((cNorm_mono_order (le_max_right 8 (s + 2))).trans_lt (hsmall.trans_le (min_le_left _ _)))
  exact hsource F hF hQF H hH (by linarith only [hFdiff, hQdiff, hmean.trans_le (min_le_left _ _)])

end JanetCartan.PhysicalInverseContinuity
