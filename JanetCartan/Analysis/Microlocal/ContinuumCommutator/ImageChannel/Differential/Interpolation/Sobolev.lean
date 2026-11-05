module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Space
public import Mathlib.Analysis.MeanInequalities

/-!
# Weighted periodic Sobolev interpolation

For `app:ch_background:eq:bg-commutator`, weighted Young's inequality on each
Fourier mode and the triangle inequality in the actual weighted sequence space
trade the lower datum norm against one high coefficient budget times L².
The proof includes order zero and does not require positive dimension.
-/

public noncomputable section

open scoped ENNReal

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem periodicSobolevWeight_young {s r : ℕ} (hs : 0 < s) (hr : r ≤ s)
    {H : ℝ} (hH : 0 ≤ H) (k : Fin n → ℤ) :
    H ^ (1 - (r : ℝ) / s) * periodicSobolevWeight r k ≤
      H + periodicSobolevWeight s k := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hθ : 0 ≤ (r : ℝ) / s := by positivity
  have hθ' : (r : ℝ) / s ≤ 1 := (div_le_one hs').mpr (by exact_mod_cast hr)
  have hw : periodicSobolevWeight r k = periodicSobolevWeight s k ^ ((r : ℝ) / s) := by
    unfold periodicSobolevWeight
    rw [← Real.rpow_natCast_mul (Real.sqrt_nonneg _)]
    rw [mul_div_cancel₀ _ hs'.ne', Real.rpow_natCast]
  rw [hw]
  have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hθ') hθ
    hH (periodicSobolevWeight_pos s k).le (by ring)
  have hw0 := (periodicSobolevWeight_pos s k).le
  nlinarith [mul_nonneg hθ hH, mul_nonneg (sub_nonneg.mpr hθ') hw0]

/-- Weighted periodic interpolation for `app:ch_background:eq:bg-commutator`,
proved on the actual weighted Fourier sequence. -/
theorem periodic_gradeNorm_weighted_interpolate {s r : ℕ} (hr : r ≤ s)
    {H : ℝ} (hH : 0 ≤ H) (u : PeriodicSobolevSpace n F s) :
    H ^ (1 - (r : ℝ) / s) *
      (periodicSobolevScale n F).gradeNorm r (toL2 s u) ≤
        ‖u‖ + H * ‖toL2 s u‖ := by
  by_cases hs : s = 0
  · have hr0 : r = 0 := by omega
    simp only [hs, hr0, Nat.cast_zero, zero_div, sub_zero, Real.rpow_one,
      GradedScale.gradeNorm_zero]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  let v : PeriodicL2 n F := toL2 s u
  have hv : v ∈ periodicSobolevLevel n F s := toL2_mem s u
  let ar := periodicSobolevAnalysis r ⟨v, antitone_periodicSobolevLevel hr hv⟩
  let az := periodicSobolevAnalysis 0 ⟨v, antitone_periodicSobolevLevel (Nat.zero_le s) hv⟩
  let atop := periodicSobolevAnalysis s ⟨v, hv⟩
  have hpoint : ‖H ^ (1 - (r : ℝ) / s) • ar‖ ≤ ‖H • az + atop‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro k
    simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply,
      ar, az, atop, periodicSobolevAnalysis_apply, weightedPeriodicL2FourierCoeff_apply,
      periodicSobolevWeight, pow_zero, one_smul]
    rw [smul_smul, ← add_smul, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (periodicSobolevWeight_young hspos hr hH k) (norm_nonneg _)
  have htri := hpoint.trans (norm_add_le (H • az) atop)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hH _), abs_of_nonneg hH] at htri
  have hlow : ‖az‖ = ‖v‖ := periodicSobolevSeminorm_zero _
  have hhigh : ‖atop‖ = ‖u‖ := rfl
  have hmid : (periodicSobolevScale n F).gradeNorm r v = ‖ar‖ :=
    (periodicSobolevScale n F).gradeNorm_eq (antitone_periodicSobolevLevel hr hv)
  rw [hmid]
  simpa only [hlow, hhigh, add_comm] using htri

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
