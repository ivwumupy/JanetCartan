module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.ScaleSums

/-!
# Summation of independent physical frequency indices

The finite dimensional threshold below absorbs carrier volumes only.
Symbol growth and output derivatives remain the responsibility of the pair
estimates in `app:ch_regular:eq:chain-tail`. All weights use the actual
physical cutoff carriers; the low graph family is retained in full.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

/-- Uniform total volume of all low graph carriers, including dimension zero
(`app:ch_regular:eq:chain-tail`). -/
theorem tsum_volume_real_lowGraphCutoff_le (n : ℕ) :
    ∑' j, volume.real (tsupport (lowGraphCutoff (n := n) j)) ≤
      3 * (2 : ℝ) ^ n * frequencyBallVolume n := by
  apply Real.tsum_le_of_sum_le (fun _ => measureReal_nonneg)
  intro s
  apply sum_volume_real_lowGraphCutoff_le s (by norm_num : (0 : ℝ) ≤ 2)
  intro j hj ξ hξ
  rw [mem_closedBall, dist_zero_right]
  apply (tsupport_lowGraphCutoff_subset j hξ).2.trans
  have hi := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ j)
  linarith

/-- A fixed inverse-power reserve turns high graph carrier volumes into a
geometric sequence (`app:ch_regular:eq:chain-tail`). -/
theorem highGraphCutoff_weighted_volume_le (j : ℕ) :
    volume.real (tsupport (highGraphCutoff (n := n) j)) / ((2 : ℝ) ^ j) ^ (n + 1) ≤
      ((4 : ℝ) ^ n * frequencyBallVolume n) * ((2 : ℝ)⁻¹) ^ j := by
  apply (div_le_div_of_nonneg_right (volume_real_tsupport_highGraphCutoff_le (n := n) j)
    (by positivity)).trans_eq
  rw [pow_add, mul_pow, pow_succ]
  simp only [inv_pow]
  norm_num only [pow_two]
  field_simp
  ring

/-- The independent output carriers satisfy a geometric weighted-volume
bound also at index zero (`app:ch_regular:eq:chain-tail`). -/
theorem outputCutoff_weighted_volume_le (k : ℕ) :
    volume.real (tsupport (outputCutoff (n := n) k)) / ((2 : ℝ) ^ k) ^ (n + 1) ≤
      ((2 : ℝ) ^ n * frequencyBallVolume n) * ((2 : ℝ)⁻¹) ^ k := by
  apply (div_le_div_of_nonneg_right (volume_real_tsupport_outputCutoff_le (n := n) k)
    (by positivity)).trans_eq
  rw [pow_succ, mul_pow, pow_succ]
  simp only [inv_pow]
  field_simp

/-- Absolute summability after the fixed dimensional volume reserve for
high graph carriers (`app:ch_regular:eq:chain-tail`). -/
theorem summable_highGraphCutoff_weighted_volume (n : ℕ) :
    Summable (fun j => volume.real (tsupport (highGraphCutoff (n := n) j)) /
      ((2 : ℝ) ^ j) ^ (n + 1)) := by
  apply ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num)).mul_left ((4 : ℝ) ^ n * frequencyBallVolume n)).of_nonneg_of_le
  · intro j; exact div_nonneg measureReal_nonneg (by positivity)
  · exact highGraphCutoff_weighted_volume_le

/-- Absolute summability of the independent output index after the same
fixed reserve (`app:ch_regular:eq:chain-tail`). -/
theorem summable_outputCutoff_weighted_volume (n : ℕ) :
    Summable (fun k => volume.real (tsupport (outputCutoff (n := n) k)) /
      ((2 : ℝ) ^ k) ^ (n + 1)) := by
  apply ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num)).mul_left ((2 : ℝ) ^ n * frequencyBallVolume n)).of_nonneg_of_le
  · intro k; exact div_nonneg measureReal_nonneg (by positivity)
  · exact outputCutoff_weighted_volume_le

/-- Independent high graph and output carrier indices are summable after
`2(n+1)` inverse powers of their larger dyadic radius. The pair-estimate
producer supplies the additional inverse powers absorbing symbol growth
and output derivatives (`app:ch_regular:eq:chain-tail`). -/
theorem summable_highGraphCutoff_outputCutoff_max_weighted_volume (n : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      volume.real (tsupport (highGraphCutoff (n := n) p.1)) *
        volume.real (tsupport (outputCutoff (n := n) p.2)) /
          (max ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2)) ^ (2 * (n + 1))) := by
  have hs := (summable_highGraphCutoff_weighted_volume n).mul_of_nonneg
    (summable_outputCutoff_weighted_volume n)
    (fun j => div_nonneg measureReal_nonneg (by positivity))
    (fun k => div_nonneg measureReal_nonneg (by positivity))
  apply hs.of_nonneg_of_le
  · intro p; exact div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (by positivity)
  · intro p
    rw [div_mul_div_comm]
    apply div_le_div_of_nonneg_left (mul_nonneg measureReal_nonneg measureReal_nonneg)
      (by positivity)
    calc
      _ ≤ (max ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2)) ^ (n + 1) *
          (max ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2)) ^ (n + 1) := by gcongr <;> simp
      _ = _ := by rw [← pow_add]; congr 1; omega

/-- For low graph frequencies there is no inverse low-radius weight: the
summable carrier volumes alone suffice, paired with independent weighted
output volumes (`app:ch_regular:eq:chain-tail`). -/
theorem summable_lowGraphCutoff_outputCutoff_weighted_volume (n : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      volume.real (tsupport (lowGraphCutoff (n := n) p.1)) *
        (volume.real (tsupport (outputCutoff (n := n) p.2)) /
          ((2 : ℝ) ^ p.2) ^ (n + 1))) :=
  (summable_volume_real_tsupport_lowGraphCutoff n).mul_of_nonneg
    (summable_outputCutoff_weighted_volume n)
    (fun _ => measureReal_nonneg) (fun _ => div_nonneg measureReal_nonneg (by positivity))

end JanetCartan.FiniteChain.Graph.PhysicalShells
