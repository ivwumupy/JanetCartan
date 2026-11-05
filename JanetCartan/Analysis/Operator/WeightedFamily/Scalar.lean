module

public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite nonnegative weights

The scalar Cauchy–Schwarz estimates behind `main:eq:primary-strain` and
`app:ch_pairs:eq:pairs-weighted-U` in `paper.tex`. All sums allow zero weights
and empty index sets. Nonnegativity is required only on the summation set.
-/

@[expose] public section

namespace JanetCartan.WeightedFamily

variable {ι : Type*} (s : Finset ι) (μ : ι → ℝ)

/-- The squared primary coefficient bound used in `main:eq:primary-strain`. -/
theorem sum_sqrt_sq_le_card_mul_sum (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    (∑ i ∈ s, Real.sqrt (μ i)) ^ 2 ≤ s.card * ∑ i ∈ s, μ i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ))
    (fun i ↦ Real.sqrt (μ i))
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_congr rfl (fun i hi ↦ Real.sq_sqrt (hμ i hi))] using h

/-- The primary coefficient bound in `main:eq:primary-strain`. -/
theorem sum_sqrt_le_sqrt_card_mul_sum (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    ∑ i ∈ s, Real.sqrt (μ i) ≤ Real.sqrt (s.card * ∑ i ∈ s, μ i) :=
  Real.le_sqrt_of_sq_le (sum_sqrt_sq_le_card_mul_sum s μ hμ)

/-- The bound `𝒲μ ≤ M Cμ` in `app:ch_pairs:prop:pairs-lag-sum`. -/
theorem sum_sqrt_sq_le_card_mul_bound (hμ : ∀ i ∈ s, 0 ≤ μ i)
    {C : ℝ} (hmass : ∑ i ∈ s, μ i ≤ C) :
    (∑ i ∈ s, Real.sqrt (μ i)) ^ 2 ≤ s.card * C :=
  (sum_sqrt_sq_le_card_mul_sum s μ hμ).trans
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _))

/-- Cauchy–Schwarz for synthesis with square-root weights, used in
`main:eq:primary-strain`; it introduces no cardinality factor. -/
theorem sum_sqrt_mul_le (hμ : ∀ i ∈ s, 0 ≤ μ i) (a : ι → ℝ) :
    ∑ i ∈ s, Real.sqrt (μ i) * a i ≤
      Real.sqrt (∑ i ∈ s, μ i) * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i ↦ Real.sqrt (μ i)) a
  simpa only [Finset.sum_congr rfl (fun i hi ↦ Real.sq_sqrt (hμ i hi))] using h

/-- Weighted Cauchy–Schwarz for the row estimates of
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`, including zero weights. -/
theorem sum_weight_mul_sq_le (hμ : ∀ i ∈ s, 0 ≤ μ i) (a b : ι → ℝ) :
    (∑ i ∈ s, μ i * a i * b i) ^ 2 ≤
      (∑ i ∈ s, μ i * a i ^ 2) * ∑ i ∈ s, μ i * b i ^ 2 := by
  have hab : ∀ i ∈ s,
      (Real.sqrt (μ i) * a i) * (Real.sqrt (μ i) * b i) = μ i * a i * b i := by
    intro i hi
    calc
      _ = (Real.sqrt (μ i)) ^ 2 * a i * b i := by ring
      _ = _ := by rw [Real.sq_sqrt (hμ i hi)]
  have hs (a : ι → ℝ) : ∀ i ∈ s, (Real.sqrt (μ i) * a i) ^ 2 = μ i * a i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hμ i hi)]
  simpa only [Finset.sum_congr rfl hab, Finset.sum_congr rfl (hs a),
    Finset.sum_congr rfl (hs b)] using
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ Real.sqrt (μ i) * a i)
      (fun i ↦ Real.sqrt (μ i) * b i)

/-- A weighted sum is bounded by mass times weighted energy, as needed in
`app:ch_mean_pairs:eq:mean-canonical-weighted-low`. -/
theorem sum_weight_mul_le (hμ : ∀ i ∈ s, 0 ≤ μ i) (a : ι → ℝ) :
    ∑ i ∈ s, μ i * a i ≤
      Real.sqrt (∑ i ∈ s, μ i) * Real.sqrt (∑ i ∈ s, μ i * a i ^ 2) := by
  have h := sum_weight_mul_sq_le s μ hμ (fun _ ↦ 1) a
  simp only [one_pow, mul_one] at h
  simpa only [Real.sqrt_mul (Finset.sum_nonneg hμ)] using Real.le_sqrt_of_sq_le h

/-- The full ordered pair coefficient sum is exactly `𝒲μ`, including doubled
carriers (`app:ch_pairs:eq:pairs-exact-offself`). -/
theorem sum_sum_sqrt_mul_eq (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    (∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j)) =
      (∑ i ∈ s, Real.sqrt (μ i)) ^ 2 := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i) * Real.sqrt (μ j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ ↦ Real.sqrt_mul (hμ i hi) (μ j))
    _ = _ := by rw [sq, Finset.sum_mul_sum]

/-- Removing the difference diagonal subtracts precisely the total mass;
this is the coefficient identity in `app:ch_pairs:eq:pairs-exact-offself`. -/
theorem sum_sum_erase_sqrt_mul_eq [DecidableEq ι] (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    (∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j)) =
      (∑ i ∈ s, Real.sqrt (μ i)) ^ 2 - ∑ i ∈ s, μ i := by
  have hdiag (i : ι) (hi : i ∈ s) : Real.sqrt (μ i * μ i) = μ i := by
    rw [← sq, Real.sqrt_sq (hμ i hi)]
  have h := Finset.sum_congr rfl (fun i hi ↦
    s.sum_erase_add (fun j ↦ Real.sqrt (μ i * μ j)) hi)
  simp only [Finset.sum_add_distrib, Finset.sum_congr rfl hdiag,
    sum_sum_sqrt_mul_eq s μ hμ] at h
  linarith

/-- The two signed coefficient sums have total at most `2𝒲μ`, with no second
sample-count loss (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem signed_pair_coefficient_sum_le [DecidableEq ι] (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    (∑ i ∈ s, ∑ j ∈ s, Real.sqrt (μ i * μ j)) +
        (∑ i ∈ s, ∑ j ∈ s.erase i, Real.sqrt (μ i * μ j)) ≤
      2 * (∑ i ∈ s, Real.sqrt (μ i)) ^ 2 := by
  rw [sum_sum_sqrt_mul_eq s μ hμ, sum_sum_erase_sqrt_mul_eq s μ hμ]
  have := Finset.sum_nonneg hμ
  linarith

end JanetCartan.WeightedFamily
