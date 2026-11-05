module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Unit cubes for the smooth pointwise Sobolev estimate

These are the averaging domains for the smoothness step in
`app:ch_regular:thm:exact-correction`, with derivative norms as in
`app:not:fourier`. Their volume is one in every dimension, so their local
L¹ norms are bounded by global L² norms without a support assumption.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- The closed unit cube with lower corner `x`, used to average the fundamental
theorem of calculus in `app:ch_regular:thm:exact-correction`. -/
def pointwiseUnitCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Icc (WithLp.ofLp x) (fun i ↦ x i + 1)

/-- The averaging cube for `app:ch_regular:thm:exact-correction` is measurable. -/
theorem measurableSet_pointwiseUnitCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (pointwiseUnitCube x) :=
  measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin n)).measurable

/-- The averaging cube for `app:ch_regular:thm:exact-correction` has unit volume,
including in dimension zero. -/
theorem volume_pointwiseUnitCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    volume (pointwiseUnitCube x) = 1 := by
  rw [pointwiseUnitCube,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      measurableSet_Icc.nullMeasurableSet]
  simp [Real.volume_Icc_pi]

/-- On the unit cube, Hölder bounds the L¹ norm by the global L² norm. This
step of `app:ch_regular:thm:exact-correction` needs no compact support. -/
theorem lintegral_enorm_pointwiseUnitCube_le_eLpNorm_two
    {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : AEStronglyMeasurable f volume) (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y in pointwiseUnitCube x, ‖f y‖ₑ) ≤ eLpNorm f 2 volume := by
  have hfm := hf.restrict (s := pointwiseUnitCube x)
  rw [← eLpNorm_one_eq_lintegral_enorm hfm]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfm
  simp only [Measure.restrict_apply_univ, volume_pointwiseUnitCube,
    ENNReal.one_rpow, mul_one] at h
  exact h.trans (eLpNorm_restrict_le f 2 volume _)

/-- Averaged FTC on one coordinate, retaining the local L¹ integrals for
iteration over a cube in `app:ch_regular:thm:exact-correction`. -/
theorem enorm_le_lintegral_unitInterval_add_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    ‖f x‖ₑ ≤ (∫⁻ y in Icc x (x + 1), ‖f y‖ₑ) +
      ∫⁻ y in Icc x (x + 1), ‖deriv f y‖ₑ := by
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
  simpa only [lintegral_const, hμ, mul_one,
    lintegral_add_right _ measurable_const] using havg

end JanetCartan.LocalSobolev.FiniteOrder
