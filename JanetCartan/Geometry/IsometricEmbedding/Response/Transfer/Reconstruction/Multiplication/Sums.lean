module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Mixed

/-!
# Finite sums for localized multiplication

The finite arithmetic needed by the multiplier induction for
`app:ch_response:eq:response-graded-displacement` and its derivative and strain
counterparts. We reuse the existing mixed Sobolev sum, but do not require its
coefficient budgets to be monotone.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Increasing the envelope order bounds the preceding mixed sum without
monotonicity of coefficient bounds, for
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem multiplier_sum_succ_le (n : ℕ) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    {u : L2} (hu : MemFourierSobolev ((n + 1 : ℕ) : ℝ) u) :
    mixedAmplitudeSobolevSum n C u ≤ mixedAmplitudeSobolevSum (n + 1) C u := by
  unfold mixedAmplitudeSobolevSum
  rw [Finset.sum_range_succ' (n := n + 1)]
  simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  apply le_trans _ (le_add_of_nonneg_right
    (mul_nonneg (hC _) (fourierSobolevNorm_nonneg _ _)))
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (fourierSobolevNorm_mono (hu.mono (by exact_mod_cast Finset.mem_range.mp hk))
      (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)) (hC _)

/-- One coefficient derivative consumes exactly one entry of the finite budget
in `app:ch_response:eq:response-reconstruction-grading`. -/
theorem multiplier_sum_shift_le (n : ℕ) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (u : L2) :
    mixedAmplitudeSobolevSum n (fun j ↦ C (j + 1)) u ≤
      mixedAmplitudeSobolevSum (n + 1) C u := by
  unfold mixedAmplitudeSobolevSum
  calc
    _ = ∑ k ∈ Finset.range (n + 1), C (n + 1 - k) * fourierSobolevNorm (k : ℝ) u := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [show n - k + 1 = n + 1 - k by have := Finset.mem_range.mp hk; omega]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ ↦ mul_nonneg (hC _) (fourierSobolevNorm_nonneg _ _))

/-- One envelope derivative costs `2π` and one Sobolev order, for
`app:ch_response:eq:response-graded-derivative`. -/
theorem multiplier_sum_derivative_le (n : ℕ) {C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) {u v : L2} {i : Fin d}
    (hv : HasEuclideanL2CoordinateDerivative i u v)
    (hu : MemFourierSobolev ((n + 1 : ℕ) : ℝ) u) :
    mixedAmplitudeSobolevSum n C v ≤
      (2 * Real.pi) * mixedAmplitudeSobolevSum (n + 1) C u := by
  unfold mixedAmplitudeSobolevSum
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (2 * Real.pi) * (C (n - k) * fourierSobolevNorm ((k : ℝ) + 1) u) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : (k : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Finset.mem_range.mp hk
      have h := mul_le_mul_of_nonneg_left
        (hv.fourierSobolevNorm_le (by positivity) (hu.mono hkn)) (hC (n - k))
      nlinarith
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_range_succ' (n := n + 1)]
      simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
      exact le_add_of_nonneg_right (mul_nonneg (hC _) (fourierSobolevNorm_nonneg _ _))

/-- The scale comparison `L ≤ K` absorbs every coefficient derivative in the
graded estimate `app:ch_response:eq:response-reconstruction-grading`.
Only envelope orders through `n` occur. -/
theorem multiplier_sum_graded_le (n : ℕ) (C B : ℕ → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    {A L K : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hLK : L ≤ K)
    (u : L2)
    (hub : ∀ p, p ≤ n → fourierSobolevNorm (p : ℝ) u ≤ B p * A * K ^ p) :
    mixedAmplitudeSobolevSum n (fun r ↦ C r * L ^ r) u ≤
      (∑ k ∈ Finset.range (n + 1), C (n - k) * B k) * A * K ^ n := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  unfold mixedAmplitudeSobolevSum
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  calc
    _ ≤ (C (n - k) * L ^ (n - k)) * (B k * A * K ^ k) :=
      mul_le_mul_of_nonneg_left (hub k hkn) (mul_nonneg (hC _) (pow_nonneg hL0 _))
    _ ≤ (C (n - k) * K ^ (n - k)) * (B k * A * K ^ k) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLK _) (hC _))
        (mul_nonneg (mul_nonneg (hB k) hA) (pow_nonneg hK0 k))
    _ = C (n - k) * B k * A * K ^ n := by
      calc
        _ = C (n - k) * B k * A * (K ^ (n - k) * K ^ k) := by ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hkn]

/-- Interpolation preserves the exact real exponent of the grading scale in
`app:ch_response:eq:response-graded-displacement`. Only two endpoint bounds
and the actual upper Sobolev membership are needed. -/
theorem multiplier_interpolate_graded {n : ℕ} (hn : 0 < n) {s K A D₀ Dₙ : ℝ} (hs : 0 ≤ s)
    (hsn : s ≤ n) (hK : 0 < K) (u : L2) (hu : MemFourierSobolev (n : ℝ) u)
    (hzero : fourierSobolevNorm 0 u ≤ D₀ * A)
    (hhigh : fourierSobolevNorm (n : ℝ) u ≤ Dₙ * A * K ^ n) :
    fourierSobolevNorm s u ≤ (D₀ + Dₙ) * A * K ^ s := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : (K ^ n : ℝ) ^ (1 - s / (n : ℝ)) = K ^ ((n : ℝ) - s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    congr 1
    field_simp
  have hp : K ^ ((n : ℝ) - s) * K ^ s = K ^ n := by
    rw [← Real.rpow_add hK, sub_add_cancel, Real.rpow_natCast]
  have h := fourierSobolevNorm_weighted_interpolate hs hsn (pow_nonneg hK.le n) hu
    (H := K ^ n)
  rw [he] at h
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hK ((n : ℝ) - s))).mp
  calc
    _ ≤ K ^ n * fourierSobolevNorm 0 u + fourierSobolevNorm (n : ℝ) u := h
    _ ≤ K ^ n * (D₀ * A) + Dₙ * A * K ^ n :=
      add_le_add (mul_le_mul_of_nonneg_left hzero (pow_nonneg hK.le n)) hhigh
    _ = K ^ ((n : ℝ) - s) * ((D₀ + Dₙ) * A * K ^ s) := by
      rw [show K ^ ((n : ℝ) - s) * ((D₀ + Dₙ) * A * K ^ s) =
        (D₀ + Dₙ) * A * (K ^ ((n : ℝ) - s) * K ^ s) by ring, hp]
      ring

end JanetCartan.IsometricEmbedding.Reconstruction
