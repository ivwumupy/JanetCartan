module

public import JanetCartan.Iteration.PhysicalBackground.Source

/-!
# Exact measured current source Sobolev bounds

The v2 source is twice the old half-normalized cut source, at the MEASUREMENT
cutoff (index one), not the old source cutoff (index zero). This module gives
its literal Sobolev norm and a physical-jet estimate with zero derivative
loss. It is the finite-low and all-order source interface for task24; proving
smallness of the current physical residual from the original initializer is
still a separate, explicit obligation.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow PositiveBackground

variable {n : ℕ} {r : ℝ}

/-- Exact v2 normalization in the SAME Sobolev scale. The physical cutoff
is index one throughout the transition region. This identity must not be
replaced by an index-zero normalized-source bound
(`app:ch_background:eq:bg-density-input`). -/
theorem measuredSourceToL2_gradeNorm (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (measuredSourceToL2 hr hcell Q R hQ hR) =
      2 * periodicSobolevNorm s
        (UniformStep.Periodization.vectorPeriodization (cutReducedSource (FixedCutoffs.physical hr 1) Q R)) := by
  let source := sourceToL2 (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
    (fixedCutReducedSource_periodic hr hcell hQ hR 1)
  have hm := sourceToL2_mem (cutReducedSource (FixedCutoffs.physical hr 1) Q R)
    (fixedCutReducedSource_periodic hr hcell hQ hR 1) s
  have he : measuredSourceToL2 hr hcell Q R hQ hR = (2 : ℝ) • source := by
    simp only [measuredSourceToL2, fixedResidualToL2, source, ← neg_smul, neg_neg]
  rw [he]
  let S := periodicSobolevScale n (Euclidean n)
  have hsm : S.gradeNorm s ((2 : ℝ) • source) = 2 * S.gradeNorm s source := by
    rw [S.gradeNorm_eq ((S.level s).smul_mem (2 : ℝ) hm), S.gradeNorm_eq hm]
    change S.seminorm s ((2 : ℝ) • (⟨source, hm⟩ : S.level s)) = _
    simpa only [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      map_smul_eq_mul (S.seminorm s) (2 : ℝ) (⟨source, hm⟩ : S.level s)
  exact hsm.trans (congrArg (2 * ·) (sourceToL2_gradeNorm _ _ s))

/-- The literal current measurement source is bounded by physical reduced
residual jets, with no derivative loss and an explicit constant. This reduces
both its finite-low smallness and high profile to the exact current physical
formula rather than assuming successful inverse-input estimates
(`app:ch_background:prop:bg-current`, finite-low neighborhood step). -/
theorem measuredSourceToL2_gradeNorm_le (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (measuredSourceToL2 hr hcell Q R hQ hR) ≤
      (2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card) *
        cNorm (closedBall 0 (4 * r)) s (cutReducedSource (FixedCutoffs.physical hr 1) Q R) := by
  have hsupp : tsupport (FixedCutoffs.physical (n := n) hr 1) ⊆ ball 0 (4 * r) := by
    apply (FixedCutoffs.physical_tsupport hr 1).trans (ball_subset_ball _)
    norm_num
    linarith
  have hc := contDiff_cutReducedSource isOpen_ball (FixedCutoffs.physical hr 1).contDiff hsupp hQ hR
  have hb := sourceToL2_gradeNorm_le hcell hc
    ((cutReducedSource_tsupport (FixedCutoffs.physical hr 1) Q R).trans
      (FixedCutoffs.physical_tsupport_four hr 1))
    (fixedCutReducedSource_periodic hr hcell hQ hR 1) s
  rw [sourceToL2_gradeNorm] at hb
  rw [measuredSourceToL2_gradeNorm]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end JanetCartan.PhysicalBackground
