module

public import JanetCartan.Analysis.Fourier.Periodic.Lattice

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bessel weights at a frequency cutoff

The squared low and high frequency weights in `app:lem:sharp-fourier-embedding`.
The constants depend only on the dimension and derivative orders.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ}

/-- Finite support makes the low Bessel weight summable
(`app:lem:sharp-fourier-embedding`). -/
theorem summable_besselWeight_low (r : ℕ) (K : ℝ) :
    Summable (fun k : Fin n → ℤ ↦
      if frequencyNorm k ≤ K then (1 + frequencyNorm k ^ 2) ^ (r : ℝ) else 0) := by
  apply summable_of_ne_finset_zero (s := frequencyBall n K)
  intro k hk
  simp only [mem_frequencyBall] at hk
  simp [hk]

private theorem sq_sqrt_mul_rpow {C K a : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    (Real.sqrt C * K ^ a) ^ 2 = C * K ^ (2 * a) := by
  rw [mul_pow, Real.sq_sqrt hC, ← Real.rpow_natCast, ← Real.rpow_mul hK]
  congr 1
  congr 1
  ring

/-- The squared low weight is bounded by `C(n,r) K^(2r+n)`
(`app:lem:sharp-fourier-embedding`), in the form used by Cauchy–Schwarz. -/
theorem tsum_besselWeight_low_le {r : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    (∑' k : Fin n → ℤ,
      if frequencyNorm k ≤ K then (1 + frequencyNorm k ^ 2) ^ (r : ℝ) else 0) ≤
        (Real.sqrt ((5 : ℝ) ^ n * 2 ^ r) * K ^ ((r : ℝ) + (n : ℝ) / 2)) ^ 2 := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [tsum_eq_sum (s := frequencyBall n K) (fun k hk ↦ by
    simp only [mem_frequencyBall] at hk
    simp [hk])]
  calc
    _ ≤ ∑ _k ∈ frequencyBall n K, (2 * K ^ 2) ^ r := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK := mem_frequencyBall.mp hk
      simp only [ite_eq_left hkK, Real.rpow_natCast]
      apply pow_le_pow_left₀ (by positivity)
      have hsq := pow_le_pow_left₀ (frequencyNorm_nonneg k) hkK 2
      have hKsq : 1 ≤ K ^ 2 := by nlinarith
      linarith
    _ = (frequencyBall n K).card * (2 * K ^ 2) ^ r := by
      simp
    _ ≤ (5 ^ n * K ^ n) * (2 * K ^ 2) ^ r :=
      mul_le_mul_of_nonneg_right (card_frequencyBall_le hK) (by positivity)
    _ = (Real.sqrt ((5 : ℝ) ^ n * 2 ^ r) * K ^ ((r : ℝ) + (n : ℝ) / 2)) ^ 2 := by
      rw [sq_sqrt_mul_rpow (by positivity) hK0, mul_pow]
      have hp : K ^ n * (K ^ 2) ^ r = K ^ (2 * ((r : ℝ) + (n : ℝ) / 2)) := by
        rw [← Real.rpow_natCast K n, ← Real.rpow_natCast (K ^ 2) r,
          ← Real.rpow_natCast K 2, ← Real.rpow_mul hK0, ← Real.rpow_add hKpos]
        congr 1
        push_cast
        ring
      calc
        _ = (5 ^ n * 2 ^ r) * (K ^ n * (K ^ 2) ^ r) := by ring
        _ = _ := by rw [hp]

private theorem besselWeight_high_le {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K) (k : Fin n → ℤ) :
    (if frequencyNorm k ≤ K then 0 else
      (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) - m)) ≤
    (if K < frequencyNorm k then frequencyNorm k ^ (-(2 * ((m : ℝ) - r))) else 0) := by
  by_cases hk : frequencyNorm k ≤ K
  · simp [hk, not_lt.mpr hk]
  · have hk' : K < frequencyNorm k := lt_of_not_ge hk
    simp only [ite_eq_right hk, ite_eq_left hk']
    have hp : 0 < frequencyNorm k := lt_of_lt_of_le zero_lt_one (hK.trans hk'.le)
    calc
      _ ≤ (frequencyNorm k ^ 2) ^ ((r : ℝ) - m) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
          (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
        congr 1
        push_cast
        ring

/-- The high Bessel weight is summable precisely in the strict range needed
for `app:lem:sharp-fourier-embedding`. -/
theorem summable_besselWeight_high {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K) :
    Summable (fun k : Fin n → ℤ ↦
      if frequencyNorm k ≤ K then 0 else (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) - m)) := by
  exact Summable.of_nonneg_of_le (fun k ↦ by split <;> positivity)
    (besselWeight_high_le hm hK)
    (summable_frequencyNorm_rpow_tail (by linarith : (n : ℝ) < 2 * ((m : ℝ) - r)) hK)

/-- The squared high weight is bounded by `C(n,r,m) K^(2r+n-2m)`
(`app:lem:sharp-fourier-embedding`), with a constant independent of `K`. -/
theorem tsum_besselWeight_high_le {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K) :
    (∑' k : Fin n → ℤ,
      if frequencyNorm k ≤ K then 0 else (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) - m)) ≤
        (Real.sqrt (frequencyTailConstant n (2 * ((m : ℝ) - r))) *
          K ^ ((r : ℝ) + (n : ℝ) / 2 - m)) ^ 2 := by
  have hp : (n : ℝ) < 2 * ((m : ℝ) - r) := by linarith
  calc
    _ ≤ ∑' k : Fin n → ℤ,
        if K < frequencyNorm k then frequencyNorm k ^ (-(2 * ((m : ℝ) - r))) else 0 :=
      (summable_besselWeight_high hm hK).tsum_le_tsum (besselWeight_high_le hm hK)
        (summable_frequencyNorm_rpow_tail hp hK)
    _ ≤ frequencyTailConstant n (2 * ((m : ℝ) - r)) *
        K ^ ((n : ℝ) - 2 * ((m : ℝ) - r)) := tsum_frequencyNorm_rpow_tail_le hp hK
    _ = _ := by
      rw [sq_sqrt_mul_rpow (frequencyTailConstant_pos hp).le (le_trans zero_le_one hK)]
      congr 2
      ring

end JanetCartan
