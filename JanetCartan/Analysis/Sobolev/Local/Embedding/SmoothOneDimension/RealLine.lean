module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# A pointwise one-dimensional Sobolev estimate

The H¹ estimate used in `app:ch_regular:thm:exact-correction` follows on the
real line by averaging the fundamental theorem of calculus over a unit interval.
The norms follow the convention in `app:not:fourier`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace JanetCartan.LocalSobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Averaging on a unit interval bounds every point value by the global H¹ norm,
as needed for `app:ch_regular:thm:exact-correction`. -/
theorem enorm_le_eLpNorm_two_add_deriv {f : ℝ → F} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    ‖f x‖ₑ ≤ eLpNorm f 2 volume + eLpNorm (deriv f) 2 volume := by
  let μ := volume.restrict (Icc x (x + 1))
  have hμ : μ univ = 1 := by simp [μ]
  have hbound (y : ℝ) (hy : y ∈ Icc x (x + 1)) :
      ‖f x‖ₑ ≤ ‖f y‖ₑ + ∫⁻ z, ‖deriv f z‖ₑ ∂μ := by
    have hd := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hy.1
    have htri : ‖f x‖ₑ ≤ ‖f y‖ₑ + ‖f y - f x‖ₑ := by
      simpa only [sub_add_cancel, enorm_sub_rev (f x) (f y)] using
        ((enorm_add_le (f x - f y) (f y)).trans_eq (add_comm _ _))
    apply htri.trans
    gcongr
    exact hd.trans (lintegral_mono_set (Icc_subset_Icc le_rfl hy.2))
  have havg := lintegral_mono_ae (μ := μ)
    (Filter.Eventually.mono (self_mem_ae_restrict measurableSet_Icc) hbound)
  have hfd : AEStronglyMeasurable (deriv f) μ :=
    (hf.continuous_deriv le_rfl).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f μ := hf.continuous.aestronglyMeasurable
  simp only [lintegral_const, hμ, mul_one,
    lintegral_add_right _ measurable_const] at havg
  rw [← eLpNorm_one_eq_lintegral_enorm hfm, ← eLpNorm_one_eq_lintegral_enorm hfd] at havg
  have hcomp {g : ℝ → F}
      (hg : AEStronglyMeasurable g μ) : eLpNorm g 1 μ ≤ eLpNorm g 2 volume := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hg
    simp only [hμ, ENNReal.one_rpow, mul_one] at h
    exact h.trans (eLpNorm_restrict_le g 2 volume _)
  exact havg.trans (add_le_add (hcomp hfm) (hcomp hfd))

end JanetCartan.LocalSobolev
