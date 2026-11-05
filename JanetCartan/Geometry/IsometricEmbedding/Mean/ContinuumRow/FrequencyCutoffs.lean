module

public import JanetCartan.Analysis.ContDiff.NestedCutoffs
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Fixed radial cutoffs for the actual continuum carrier

The high-frequency cutoff has the exact plateaus of
`app:ch_background:defn:bg-row`. The compact radial regularization is fixed
before the immersion, initial data and truncation radius. These are the
functions `h` and `κ` in the released global carrier-normal constructor.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.FixedCutoffs

/-- The literal high-frequency cutoff of `app:ch_background:defn:bg-row`. -/
def highFrequency (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

/-- Smoothness of the fixed high-frequency mask (`app:ch_background:eq:bg-T`). -/
theorem highFrequency_smooth : ContDiff ℝ ∞ highFrequency :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- Exact low-frequency removal (`app:ch_background:defn:bg-row`). -/
theorem highFrequency_zero {t : ℝ} (ht : t ≤ 1) : highFrequency t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Exact high-frequency plateau (`app:ch_background:defn:bg-row`). -/
theorem highFrequency_one {t : ℝ} (ht : 2 ≤ t) : highFrequency t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The high-frequency mask is a nonnegative contraction
(`app:ch_background:defn:bg-row`). -/
theorem highFrequency_mem_Icc (t : ℝ) : highFrequency t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Fixed compact radial mask for removing the frequency regularization in
`app:ch_background:prop:bg-frame`, Step 1. -/
def radialRegularization : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The actual regularization is smooth (`app:ch_background:prop:bg-frame`). -/
theorem radialRegularization_smooth : ContDiff ℝ ∞ radialRegularization :=
  radialRegularization.contDiff

/-- Compact support of the actual radial mask
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem radialRegularization_compact : HasCompactSupport radialRegularization :=
  radialRegularization.hasCompactSupport

/-- The radial mask preserves every frequency below its truncation radius
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem radialRegularization_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    radialRegularization t = 1 := by
  have hm : t ∈ closedBall (0 : ℝ) 1 := by
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  exact radialRegularization.one_of_mem_closedBall hm

/-- The finite regularizations preserve the nonnegative amplitude convention
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem radialRegularization_mem_Icc (t : ℝ) :
    radialRegularization t ∈ Icc (0 : ℝ) 1 :=
  ⟨radialRegularization.nonneg, radialRegularization.le_one⟩

end JanetCartan.ContinuumRow.FixedCutoffs
