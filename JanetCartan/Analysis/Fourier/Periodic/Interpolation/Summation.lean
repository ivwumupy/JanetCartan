module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Summation estimates for Fourier interpolation

The Cauchy–Schwarz and frequency splitting steps of
`app:lem:sharp-fourier-embedding`. All infinite sums have explicit summability
hypotheses, or summability is proved as part of the conclusion.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- Cauchy–Schwarz for nonnegative series, including summability of the dominated
series; used in `app:lem:sharp-fourier-embedding`. -/
theorem summable_and_tsum_le_sqrt_mul_sqrt {ι : Type*} {t a b : ι → ℝ}
    (ht : ∀ i, 0 ≤ t i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, t i ^ 2 ≤ a i * b i) (hsa : Summable a) (hsb : Summable b) :
    Summable t ∧ (∑' i, t i) ≤ Real.sqrt (∑' i, a i) * Real.sqrt (∑' i, b i) := by
  have hfinite (s : Finset ι) :
      ∑ i ∈ s, t i ≤ Real.sqrt (∑' i, a i) * Real.sqrt (∑' i, b i) := by
    have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ ↦ ha i) (fun i _ ↦ hb i) (fun i _ ↦ hab i)
    have hsum : (∑ i ∈ s, a i) * (∑ i ∈ s, b i) ≤
        (∑' i, a i) * (∑' i, b i) :=
      mul_le_mul (hsa.sum_le_tsum s (fun i _ ↦ ha i))
        (hsb.sum_le_tsum s (fun i _ ↦ hb i))
        (Finset.sum_nonneg fun i _ ↦ hb i) (tsum_nonneg ha)
    exact (Real.le_sqrt_of_sq_le (hsq.trans hsum)).trans_eq
      (Real.sqrt_mul (tsum_nonneg ha) _)
  exact ⟨summable_of_sum_le ht hfinite, Real.tsum_le_of_sum_le ht hfinite⟩

/-- The low/high frequency Cauchy–Schwarz split in
`app:lem:sharp-fourier-embedding`, for a positive squared frequency weight `ρ`.
The predicate `low` selects the low frequencies. -/
theorem summable_weighted_sqrt_and_le_split {ι : Type*}
    (low : ι → Prop) [DecidablePred low] {ρ e : ι → ℝ} {r m : ℝ}
    (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 ≤ e i)
    (hlow : Summable (fun i ↦ if low i then ρ i ^ r else 0))
    (hhigh : Summable (fun i ↦ if low i then 0 else ρ i ^ (r - m)))
    (henergy : Summable e) (hweighted : Summable (fun i ↦ ρ i ^ m * e i)) :
    Summable (fun i ↦ ρ i ^ (r / 2) * Real.sqrt (e i)) ∧
      (∑' i, ρ i ^ (r / 2) * Real.sqrt (e i)) ≤
        Real.sqrt (∑' i, if low i then ρ i ^ r else 0) * Real.sqrt (∑' i, e i) +
        Real.sqrt (∑' i, if low i then 0 else ρ i ^ (r - m)) *
          Real.sqrt (∑' i, ρ i ^ m * e i) := by
  have hsq (i : ι) : (ρ i ^ (r / 2) * Real.sqrt (e i)) ^ 2 = ρ i ^ r * e i := by
    rw [mul_pow, Real.sq_sqrt (he i), ← Real.rpow_natCast,
      ← Real.rpow_mul (hρ i).le]
    congr 2
    ring
  have h₀ := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun i ↦ if low i then ρ i ^ (r / 2) * Real.sqrt (e i) else 0)
    (a := fun i ↦ if low i then ρ i ^ r else 0) (b := e)
    (fun i ↦ by have := hρ i; split <;> positivity)
    (fun i ↦ by have := hρ i; split <;> positivity) he
    (fun i ↦ by
      split
      · exact (hsq i).le
      · simp) hlow henergy
  have h₁ := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun i ↦ if low i then 0 else ρ i ^ (r / 2) * Real.sqrt (e i))
    (a := fun i ↦ if low i then 0 else ρ i ^ (r - m))
    (b := fun i ↦ ρ i ^ m * e i)
    (fun i ↦ by have := hρ i; split <;> positivity)
    (fun i ↦ by have := hρ i; split <;> positivity)
    (fun i ↦ mul_nonneg (Real.rpow_nonneg (hρ i).le _) (he i))
    (fun i ↦ by
      split
      · simp
      · rw [hsq, ← mul_assoc, ← Real.rpow_add (hρ i), sub_add_cancel])
    hhigh hweighted
  have hsplit : (fun i ↦ ρ i ^ (r / 2) * Real.sqrt (e i)) =
      (fun i ↦ (if low i then ρ i ^ (r / 2) * Real.sqrt (e i) else 0) +
        (if low i then 0 else ρ i ^ (r / 2) * Real.sqrt (e i))) := by
    funext i
    split <;> simp
  rw [hsplit]
  exact ⟨h₀.1.add h₁.1, by rw [h₀.1.tsum_add h₁.1]; exact add_le_add h₀.2 h₁.2⟩

end JanetCartan
