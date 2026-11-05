module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.Support
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Volumes of physical frequency carriers

The low-frequency volume sum in `app:ch_regular:eq:chain-tail` includes
every contracting annulus. Dimension zero is handled by empty graph carriers,
not by a false geometric-series argument with ratio one.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
variable {n : ℕ}

/-- The fixed dimensional volume constant for the frequency carriers in
`app:ch_regular:eq:chain-tail`. -/
def frequencyBallVolume (n : ℕ) : ℝ := volume.real (closedBall (0 : Euclidean n) 1)

/-- The dimensional volume constant is nonnegative
(`app:ch_regular:eq:chain-tail`). -/
theorem frequencyBallVolume_nonneg (n : ℕ) : 0 ≤ frequencyBallVolume n := measureReal_nonneg

/-- Exact volume scaling, including dimension zero, for the carriers used in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem volume_real_frequency_closedBall {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall (0 : Euclidean n) R) = R ^ n * frequencyBallVolume n := by
  simpa [frequencyBallVolume, Euclidean] using
    Measure.addHaar_real_closedBall' (volume : Measure (Euclidean n)) (0 : Euclidean n) hR

/-- High graph carrier volume, with its actual physical scale
(`app:ch_regular:eq:chain-tail`). -/
theorem volume_real_tsupport_highGraphCutoff_le (j : ℕ) :
    volume.real (tsupport (highGraphCutoff (n := n) j)) ≤
      ((2 : ℝ) ^ (j + 2)) ^ n * frequencyBallVolume n := by
  rw [← volume_real_frequency_closedBall (by positivity)]
  apply measureReal_mono _ (isCompact_closedBall _ _).measure_ne_top
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right] using (tsupport_highGraphCutoff_subset j hξ).2

/-- Low graph carrier volume decays geometrically, while its lower radius
continues to approach zero (`app:ch_regular:eq:chain-tail`). -/
theorem volume_real_tsupport_lowGraphCutoff_le (j : ℕ) :
    volume.real (tsupport (lowGraphCutoff (n := n) j)) ≤
      (2 * ((2 : ℝ) ^ j)⁻¹) ^ n * frequencyBallVolume n := by
  rw [← volume_real_frequency_closedBall (by positivity)]
  apply measureReal_mono _ (isCompact_closedBall _ _).measure_ne_top
  intro ξ hξ
  simpa only [mem_closedBall, dist_zero_right] using (tsupport_lowGraphCutoff_subset j hξ).2

/-- A uniform output carrier bound includes the zeroth ball and all positive
output annuli (`app:ch_regular:eq:chain-tail`). -/
theorem volume_real_tsupport_outputCutoff_le (k : ℕ) :
    volume.real (tsupport (outputCutoff (n := n) k)) ≤
      ((2 : ℝ) ^ (k + 1)) ^ n * frequencyBallVolume n := by
  cases k with
  | zero =>
    simp only [Nat.zero_add, pow_one]
    rw [← volume_real_frequency_closedBall (by norm_num : (0 : ℝ) ≤ 2)]
    exact measureReal_mono tsupport_outputCutoff_zero_subset
      (isCompact_closedBall _ _).measure_ne_top
  | succ k => exact volume_real_tsupport_highGraphCutoff_le k

/-- There are no graph frequencies in dimension zero, so the contracting
carriers are empty (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_lowGraphCutoff_dimension_zero (j : ℕ) :
    tsupport (lowGraphCutoff (n := 0) j) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ξ hξ
  have hzero : ξ = 0 := Subsingleton.elim _ _
  exact zero_notMem_tsupport_lowGraphCutoff j (hzero ▸ hξ)

/-- Explicit geometric majorant for the low-frequency carrier volumes
(`app:ch_regular:eq:chain-tail`). -/
theorem volume_real_tsupport_lowGraphCutoff_le_geometric (j : ℕ) :
    volume.real (tsupport (lowGraphCutoff (n := n) j)) ≤
      ((2 : ℝ) ^ n * frequencyBallVolume n) * (((2 : ℝ)⁻¹) ^ n) ^ j := by
  convert volume_real_tsupport_lowGraphCutoff_le (n := n) j using 1
  simp only [mul_pow, inv_pow, ← pow_mul, Nat.mul_comm j n]
  ring

/-- Summable low-frequency carriers in every dimension. In positive dimension
the ratio is `2^(-n)`; in dimension zero every graph carrier is empty. This
is the small-frequency summation input for `app:ch_regular:eq:chain-tail`. -/
theorem summable_volume_real_tsupport_lowGraphCutoff (n : ℕ) :
    Summable (fun j => volume.real (tsupport (lowGraphCutoff (n := n) j))) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [tsupport_lowGraphCutoff_dimension_zero, measureReal_empty] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  · have hs := (summable_geometric_of_lt_one
      (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ n)
      (pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num) hn.ne')).mul_left ((2 : ℝ) ^ n * frequencyBallVolume n)
    exact hs.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (volume_real_tsupport_lowGraphCutoff_le_geometric (n := n))

end JanetCartan.FiniteChain.Graph.PhysicalShells
