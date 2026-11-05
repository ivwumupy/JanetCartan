module

public import JanetCartan.Analysis.Fourier.Periodic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Integer Sobolev weights

The algebraic comparison underlying Appendix A and
`app:ch_regular_base:lem:ball-extension`. A multiindex of degree at most `m`
is stored with an extra `none` coordinate recording its unused degree.
Thus each Cartesian derivative occurs exactly once, without multiplicity.
The comparison constants for squared norms are `1` and `m!`.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan

/-- Appendix A: multiindices of degree at most `m`, with the unused degree at `none`. -/
def sobolevMultiindices (n m : ℕ) : Finset (Option (Fin n) → ℕ) :=
  Finset.piAntidiag Finset.univ m

/-- The slack-coordinate encoding has precisely total degree `m` (Appendix A). -/
theorem mem_sobolevMultiindices {n m : ℕ} {α : Option (Fin n) → ℕ} :
    α ∈ sobolevMultiindices n m ↔ α none + ∑ i, α (some i) = m := by
  simp [sobolevMultiindices, Finset.mem_piAntidiag, Fintype.sum_option]

/-- The slack-coordinate representation is in bijection with ordinary multiindices
of total degree at most `m`; in particular it counts each derivative once
(Appendix A; `app:ch_regular_base:lem:ball-extension`). -/
def sobolevMultiindexEquiv (n m : ℕ) :
    {α // α ∈ sobolevMultiindices n m} ≃ {β : Fin n → ℕ // ∑ i, β i ≤ m} where
  toFun α := ⟨fun i ↦ α.val (some i), by
    have h := mem_sobolevMultiindices.mp α.property
    change (∑ i, α.val (some i)) ≤ m
    omega⟩
  invFun β := ⟨Option.elim' (m - ∑ i, β.val i) β.val, by
    rw [mem_sobolevMultiindices]
    simpa using Nat.sub_add_cancel β.property⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have h := mem_sobolevMultiindices.mp α.property
      change m - ∑ i, α.val (some i) = α.val none
      omega
    | some i => rfl
  right_inv β := rfl

/-- Appendix A: the squared Fourier multiplier of a Cartesian derivative.
The unit torus has physical coordinate frequencies `2 * π * k i`. -/
def sobolevMonomial {n : ℕ} (α : Option (Fin n) → ℕ) (k : Fin n → ℤ) : ℝ :=
  ∏ i, ((2 * Real.pi * (k i : ℝ)) ^ 2) ^ α (some i)

/-- Appendix A: the multiplier obtained by summing all Cartesian derivative energies. -/
def sobolevDerivativeWeight {n : ℕ} (m : ℕ) (k : Fin n → ℤ) : ℝ :=
  ∑ α ∈ sobolevMultiindices n m, sobolevMonomial α k

/-- Squared coordinate frequencies sum to the shared squared frequency (Appendix A). -/
theorem frequencyNorm_sq_eq_sum {n : ℕ} (k : Fin n → ℤ) :
    frequencyNorm k ^ 2 = ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 := by
  simp only [frequencyNorm, mul_pow, EuclideanSpace.real_norm_sq_eq,
    ← Finset.mul_sum]

/-- The multinomial expansion of the integer Bessel weight (Appendix A). -/
theorem sobolevWeight_eq_multinomial_sum {n : ℕ} (m : ℕ) (k : Fin n → ℤ) :
    (1 + frequencyNorm k ^ 2) ^ m =
      ∑ α ∈ sobolevMultiindices n m,
        (Nat.multinomial Finset.univ α : ℝ) * sobolevMonomial α k := by
  let x : Option (Fin n) → ℝ := fun i ↦
    match i with
    | none => 1
    | some i => (2 * Real.pi * (k i : ℝ)) ^ 2
  have hx : ∑ i, x i = 1 + frequencyNorm k ^ 2 := by
    rw [Fintype.sum_option, frequencyNorm_sq_eq_sum]
  rw [← hx, Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro α _
  simp [x, Fintype.prod_option, sobolevMonomial]

/-- Every squared derivative multiplier is nonnegative (Appendix A). -/
theorem sobolevMonomial_nonneg {n : ℕ} (α : Option (Fin n) → ℕ) (k : Fin n → ℤ) :
    0 ≤ sobolevMonomial α k := by
  unfold sobolevMonomial
  exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg (sq_nonneg _) _

/-- The sum of squared derivative multipliers is nonnegative (Appendix A). -/
theorem sobolevDerivativeWeight_nonneg {n : ℕ} (m : ℕ) (k : Fin n → ℤ) :
    0 ≤ sobolevDerivativeWeight m k :=
  Finset.sum_nonneg fun _ _ ↦ sobolevMonomial_nonneg _ _

/-- The derivative weight is bounded by the integer Bessel weight, with constant `1`
(Appendix A; `app:ch_regular_base:lem:ball-extension`). -/
theorem sobolevDerivativeWeight_le {n : ℕ} (m : ℕ) (k : Fin n → ℤ) :
    sobolevDerivativeWeight m k ≤ (1 + frequencyNorm k ^ 2) ^ m := by
  rw [sobolevWeight_eq_multinomial_sum]
  apply Finset.sum_le_sum
  intro α _
  have h : (1 : ℝ) ≤ Nat.multinomial Finset.univ α := by
    exact_mod_cast Nat.multinomial_pos Finset.univ α
  simpa using mul_le_mul_of_nonneg_right h (sobolevMonomial_nonneg α k)

/-- The integer Bessel weight is bounded by `m!` times the derivative weight
(Appendix A; `app:ch_regular_base:lem:ball-extension`). -/
theorem sobolevWeight_le_factorial_mul {n : ℕ} (m : ℕ) (k : Fin n → ℤ) :
    (1 + frequencyNorm k ^ 2) ^ m ≤ (m.factorial : ℝ) * sobolevDerivativeWeight m k := by
  rw [sobolevWeight_eq_multinomial_sum, sobolevDerivativeWeight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α hα
  have hsum : ∑ i, α i = m := (Finset.mem_piAntidiag.mp hα).1
  have h : Nat.multinomial Finset.univ α ≤ m.factorial := by
    simpa [Nat.multinomial, hsum] using
      Nat.div_le_self m.factorial (∏ i, (α i).factorial)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sobolevMonomial_nonneg α k)

/-- Summability of the two integer Sobolev weights is equivalent. This statement
includes summability explicitly; it does not use a totalized divergent series
(Appendix A; `app:ch_regular_base:lem:ball-extension`). -/
theorem summable_sobolevDerivativeWeight_iff {n : ℕ} (m : ℕ)
    (a : (Fin n → ℤ) → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Summable (fun k ↦ sobolevDerivativeWeight m k * a k) ↔
      Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ m * a k) := by
  constructor
  · intro h
    apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (by positivity) (ha k))
      (fun k ↦ ?_) (h.mul_left (m.factorial : ℝ))
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (sobolevWeight_le_factorial_mul m k) (ha k)
  · intro h
    exact Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (sobolevDerivativeWeight_nonneg m k) (ha k))
      (fun k ↦ mul_le_mul_of_nonneg_right (sobolevDerivativeWeight_le m k) (ha k)) h

/-- Each individual derivative multiplier is summable when the integer Sobolev
weight is summable (Appendix A). -/
theorem summable_sobolevMonomial {n : ℕ} (m : ℕ)
    (a : (Fin n → ℤ) → ℝ) (ha : ∀ k, 0 ≤ a k)
    (h : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ m * a k))
    {α : Option (Fin n) → ℕ} (hα : α ∈ sobolevMultiindices n m) :
    Summable (fun k ↦ sobolevMonomial α k * a k) := by
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (sobolevMonomial_nonneg α k) (ha k)) (fun k ↦ ?_) h
  apply mul_le_mul_of_nonneg_right _ (ha k)
  exact (Finset.single_le_sum (fun β _ ↦ sobolevMonomial_nonneg β k) hα).trans
    (sobolevDerivativeWeight_le m k)

/-- Interchange of the derivative-index sum and the Fourier series, justified by
summability (Appendix A). -/
theorem tsum_sobolevDerivativeWeight {n : ℕ} (m : ℕ)
    (a : (Fin n → ℤ) → ℝ) (ha : ∀ k, 0 ≤ a k)
    (h : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ m * a k)) :
    (∑' k, sobolevDerivativeWeight m k * a k) =
      ∑ α ∈ sobolevMultiindices n m, ∑' k, sobolevMonomial α k * a k := by
  simp only [sobolevDerivativeWeight, Finset.sum_mul]
  exact Summable.tsum_finsetSum fun _ hα ↦ summable_sobolevMonomial m a ha h hα

/-- Comparison of the sums of squared Fourier multipliers, with the exact constants
`1` and `m!` (Appendix A; `app:ch_regular_base:lem:ball-extension`). -/
theorem tsum_sobolevWeight_comparison {n : ℕ} (m : ℕ)
    (a : (Fin n → ℤ) → ℝ) (ha : ∀ k, 0 ≤ a k)
    (h : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ m * a k)) :
    (∑' k, sobolevDerivativeWeight m k * a k) ≤
        (∑' k, (1 + frequencyNorm k ^ 2) ^ m * a k) ∧
      (∑' k, (1 + frequencyNorm k ^ 2) ^ m * a k) ≤
        (m.factorial : ℝ) * ∑' k, sobolevDerivativeWeight m k * a k := by
  have hD := (summable_sobolevDerivativeWeight_iff m a ha).mpr h
  constructor
  · exact Summable.tsum_le_tsum
      (fun k ↦ mul_le_mul_of_nonneg_right (sobolevDerivativeWeight_le m k) (ha k)) hD h
  · rw [← hD.tsum_mul_left]
    apply Summable.tsum_le_tsum (fun k ↦ ?_) h (hD.mul_left _)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (sobolevWeight_le_factorial_mul m k) (ha k)

end JanetCartan
