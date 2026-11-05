module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs

/-!
# The original radial high-pass in the sampling mask interface

The norm pullback is smooth at zero because the literal high-pass vanishes
through radius one. Its product with the normalized original direction mask
is a contraction. These are concrete mask inputs of the retained product
constructor; the full transition to its plateau at radius two is retained.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ContinuumRow ContinuumRow.CanonicalConic RawPrimary.MaskProfiles

/-- Smoothness of the SAME continuum high-pass on the transverse frequency
space, including the origin (`app:ch_background:defn:bg-row`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem contDiff_originalConicHighPass (n : ℕ) :
    ContDiff ℝ ∞ (fun η : Euclidean (n - 1) ↦ FixedCutoffs.highFrequency ‖η‖) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst η
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : Euclidean (n - 1)) (by norm_num : (0 : ℝ) < 1)] with η hη
    exact FixedCutoffs.highFrequency_zero (mem_ball_zero_iff.mp hη).le
  · exact FixedCutoffs.highFrequency_smooth.contDiffAt.comp η (contDiffAt_id.norm ℝ hη)

/-- The literal original angular/high-pass product is bounded by one at
every frequency, with no new bounding mask (`app:ch_waves:eq:B-bounds`). -/
theorem norm_originalConicDetectorMask_le_one {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (η : Euclidean (n - 1)) :
    ‖detectorMask (originalConicDetector hηb hr)
      (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖) η‖ ≤ 1 := by
  simp only [detectorMask, originalConicDetector, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ContDiffBump.nonneg _), abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc _).1]
  exact (mul_le_of_le_one_left (FixedCutoffs.highFrequency_mem_Icc _).1
    (ContDiffBump.le_one _)).trans (FixedCutoffs.highFrequency_mem_Icc _).2

end JanetCartan.Sampling
