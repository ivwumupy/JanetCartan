module

public import JanetCartan.Analysis.ContDiff.DerivativeBounds.Algebra

/-!
# Real positive-part budgets

These are the literal real inequalities in `new:eq:plus-subadditive` and
`app:eq:graded-composition-budget`. The native `HasDerivativeProfile` API
uses natural-number reserve indices; the numerical manuscript inequalities
also hold for real reserves, without rounding them.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.DerivativeBounds

private theorem two_positive_excesses_le {a b R : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R) :
    max (a - R) 0 + max (b - R) 0 ≤ max (a + b - R) 0 := by
  rcases le_total a R with h | h <;> rcases le_total b R with h' | h'
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h'), zero_add]
    exact le_max_right _ _
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h'), zero_add]
    exact (by linarith : b - R ≤ a + b - R).trans (le_max_left _ _)
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h'), add_zero]
    exact (by linarith : a - R ≤ a + b - R).trans (le_max_left _ _)
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h')]
    exact (by linarith : (a - R) + (b - R) ≤ a + b - R).trans (le_max_left _ _)

/-- The literal positive-part inequality of `new:eq:plus-subadditive` for
real nonnegative orders and reserve, including the empty family. -/
theorem sum_real_positive_excess_le {ι : Type*} (s : Finset ι) (j : ι → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hj : ∀ i ∈ s, 0 ≤ j i) :
    (∑ i ∈ s, max (j i - R) 0) ≤ max ((∑ i ∈ s, j i) - R) 0 := by
  classical
  revert hj
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hj
    have hjs : ∀ i ∈ s, 0 ≤ j i := fun i hi ↦ hj i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl (ih hjs)).trans
      (two_positive_excesses_le (hj a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg hjs) hR)

/-- The real-reserve composition budget of
`app:eq:graded-composition-budget`. Every inner derivative has order at
least one; the outer derivative order is the number of those factors. -/
theorem real_composition_reserve_le {ι : Type*} (s : Finset ι) (j : ι → ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hj : ∀ i ∈ s, 1 ≤ j i) :
    max ((s.card : ℝ) - R) 0 + (∑ i ∈ s, max (j i - R) 0) ≤
      max ((∑ i ∈ s, j i) - R) 0 := by
  by_cases hcard : (s.card : ℝ) ≤ R
  · rw [max_eq_right (sub_nonpos.mpr hcard), zero_add]
    exact sum_real_positive_excess_le s j (zero_le_one.trans hR)
      (fun i hi ↦ zero_le_one.trans (hj i hi))
  · rw [max_eq_left (sub_nonneg.mpr (not_le.mp hcard).le)]
    have hsum : (∑ i ∈ s, max (j i - R) 0) ≤ (∑ i ∈ s, j i) - s.card := by
      calc
        _ ≤ ∑ i ∈ s, (j i - 1) := Finset.sum_le_sum (fun i hi ↦
          max_le (by linarith) (by linarith [hj i hi]))
        _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc
      _ ≤ ((s.card : ℝ) - R) + ((∑ i ∈ s, j i) - s.card) := add_le_add le_rfl hsum
      _ = (∑ i ∈ s, j i) - R := by ring
      _ ≤ _ := le_max_left _ _

/-- `app:eq:graded-composition-budget` for an actual Faà di Bruno
partition, without an integrality assumption on the reserve. -/
theorem partition_real_composition_reserve_le {n : ℕ} (p : OrderedFinpartition n)
    {R : ℝ} (hR : 1 ≤ R) :
    max ((p.length : ℝ) - R) 0 + (∑ i, max ((p.partSize i : ℝ) - R) 0) ≤
      max ((n : ℝ) - R) 0 := by
  have h := real_composition_reserve_le Finset.univ (fun i ↦ (p.partSize i : ℝ)) hR
    (fun i _ ↦ by exact_mod_cast p.partSize_pos i)
  simpa only [Finset.card_univ, Fintype.card_fin, ← Nat.cast_sum,
    CompositionBounds.sum_partSize] using h

/-- The real-power version of the finite product estimate, retaining the
literal positive part and the same scale
(`app:ch_regular_base:eq:joint-primitive-product`). -/
theorem finite_product_real_reserve_bound {ι : Type*} (s : Finset ι)
    (j a C : ι → ℝ) {T R : ℝ} (hT : 1 ≤ T) (hR : 0 ≤ R)
    (hj : ∀ i ∈ s, 0 ≤ j i) (ha : ∀ i ∈ s, 0 ≤ a i) (hC : ∀ i ∈ s, 0 ≤ C i)
    (hbound : ∀ i ∈ s, a i ≤ C i * T ^ (max (j i - R) 0)) :
    (∏ i ∈ s, a i) ≤ (∏ i ∈ s, C i) * T ^ (max ((∑ i ∈ s, j i) - R) 0) := by
  calc
    _ ≤ ∏ i ∈ s, C i * T ^ (max (j i - R) 0) := Finset.prod_le_prod₀ ha hbound
    _ = (∏ i ∈ s, C i) * T ^ (∑ i ∈ s, max (j i - R) 0) := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (zero_lt_one.trans_le hT)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (sum_real_positive_excess_le s j hR hj))
      (Finset.prod_nonneg hC)

end JanetCartan.DerivativeBounds
