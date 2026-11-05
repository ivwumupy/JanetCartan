module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Derivatives
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Raw synthesis bounds at a prescribed ceiling

The two estimates in `app:ch_waves:eq:B-bounds`, for geometric radii `2^ℓ`
with final dyadic ceiling at most `C K`. All constants are independent of the
number of annuli. The masks, including detector/high-pass masks, enter only
through measurability and their uniform bound. Instantiating these hypotheses
for the actual wave family belongs to the raw-primary/current-canonical owners.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawInputRealization

variable {n J : ℕ} {β : Fin J → Euclidean (n - 1) → ℂ}

/-- The raw Fourier `L¹` estimate with the paper's ceiling parameter `K`
(`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_ceiling_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i η, ‖β i η‖ ≤ M) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hceil : (2 : ℝ) ^ J ≤ C * K)
    (v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)) :
    (∫ η, ‖density β v η‖) ≤
      (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ := by
  apply (integral_norm_density_dyadic_le hn hβ hM0 hM v).trans
  calc
    _ ≤ (M * Real.sqrt (unitBallVolume n)) * (C * K) ^ ((n : ℝ) / 2) * ‖v‖ := by
      gcongr
    _ = _ := by rw [Real.mul_rpow hC hK]; ring

/-- The initial `C^m` norm on any set, using the shared sum-of-suprema convention.
No compactness assumption is needed: all derivatives are bounded globally.
The explicit constant `(m+1) M sqrt(vol B₁) C^(m+n/2)` is independent of `J`
(`app:ch_waves:eq:B-bounds`). -/
theorem cNorm_field_ceiling_le (hn : 1 ≤ n)
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i η, ‖β i η‖ ≤ M) {C K : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hceil : (2 : ℝ) ^ J ≤ C * K)
    (v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val))
    (m : ℕ) (s : Set (Euclidean (n - 1))) :
    cNorm s m (field β v) ≤
      (((m + 1 : ℕ) : ℝ) * M * Real.sqrt (unitBallVolume n) *
        C ^ ((m : ℝ) + (n : ℝ) / 2)) * K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
  let B : ℝ := M * Real.sqrt (unitBallVolume n) *
    (C * K) ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : ∀ r ≤ m, ∀ x : Euclidean (n - 1), ‖iteratedFDeriv ℝ r (field β v) x‖ ≤ B := by
    intro r hr x
    apply (norm_iteratedFDeriv_field_dyadic_le hn hβ hM0 hM v r x).trans
    have he : ((2 : ℝ) ^ J) ^ ((r : ℝ) + (n : ℝ) / 2) ≤
        ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      linarith [show (r : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr hr]
    have hc : ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) ≤
        (C * K) ^ ((m : ℝ) + (n : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hceil (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (he.trans hc) (mul_nonneg hM0 (Real.sqrt_nonneg _))) (norm_nonneg _)
  calc
    _ ≤ ∑ _r ∈ Finset.range (m + 1), B :=
      cNorm_le_sum_of_bounds (fun _ _ ↦ hB) (fun r hr x _ ↦ hd r hr x)
    _ = (((m + 1 : ℕ) : ℝ) * M * Real.sqrt (unitBallVolume n) *
        C ^ ((m : ℝ) + (n : ℝ) / 2)) * K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, B,
        Real.mul_rpow hC (zero_le_one.trans hK)]
      ring

end JanetCartan.RawInputRealization
