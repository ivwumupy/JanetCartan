module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.RefinementSpaces
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Rounding

/-!
# Power sums for the fixed two-shell refinement

These estimates feed the Fourier and Hilbert bounds in `RefinedEstimates`,
for `app:ch_waves:eq:B-bounds` and `app:ch_waves:eq:individual-raw-slice`.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawInputPartition
open RawInputRealization

/-- Positivity of each literal refined annular radius, used in the channel
constants of `app:ch_waves:eq:B-bounds`. -/
theorem refinedRadius_pos {J : ℕ} (i : RefinedIndex J) : 0 < refinedRadius i := by
  unfold refinedRadius
  positivity

/-- The second component of the last band still lies at the ceiling `2^J`
(`app:ch_waves:eq:B-bounds`). -/
theorem refinedRadius_le_ceiling {J : ℕ} (i : RefinedIndex J) :
    refinedRadius i ≤ (2 : ℝ) ^ J := by
  apply pow_le_pow_right₀ (by norm_num)
  have h₁ := i.1.isLt
  have h₂ := i.2.isLt
  omega

/-- The two complex components give the fixed factor `1 + 2^p` in the
geometric power sum (`app:ch_waves:eq:B-bounds`). -/
theorem sum_refinedRadius_pow (p J : ℕ) :
    (∑ i : RefinedIndex J, refinedRadius i ^ p) =
      (1 + (2 : ℝ) ^ p) * ∑ j : Fin J, ((2 : ℝ) ^ j.val) ^ p := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, refinedRadius, Fin.val_zero, Fin.val_one,
    Nat.add_zero, pow_succ, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive integer power sums have constants independent of the scale count;
consumed by the Fourier bound and, at `p = 1`, by the Hilbert synthesis bound
(`app:ch_waves:eq:B-bounds`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem sum_refinedRadius_pow_le {p : ℕ} (hp : 1 ≤ p) (J : ℕ) :
    (∑ i : RefinedIndex J, refinedRadius i ^ p) ≤
      (1 + (2 : ℝ) ^ p) * ((2 : ℝ) ^ J) ^ p := by
  rw [sum_refinedRadius_pow]
  exact mul_le_mul_of_nonneg_left (sum_dyadic_radii_pow_le hp J) (by positivity)

/-- The actual rounded cutoff supplies the ceiling constant four required by
the refined Fourier and Hilbert estimates (`app:ch_waves:eq:B-bounds`). -/
theorem cutoffCount_ceiling {K : ℝ} (hK : 1 ≤ K) :
    (2 : ℝ) ^ cutoffCount K ≤ 4 * K := by
  have h := (cutoffCount_plateau hK).2
  unfold dyadicScale at h
  linarith

end JanetCartan.RawInputPartition
