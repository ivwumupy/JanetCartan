module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Partitions

/-!
# The total derivative reserve in products and composition

The existing `GradedPrimitives.sum_sub_reserve_le` is the natural-number
form of `new:eq:plus-subadditive`. Composition also counts the order of the
outer derivative. Its exact budget requires reserve at least one and is
proved here without increasing the derivative order or decreasing the reserve.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.DerivativeBounds
open ResponseTransfer.GradedPrimitives

/-- The Faà di Bruno partition budget in
`app:eq:graded-composition-budget`. Both the outer derivative and all inner
derivatives retain the SAME natural reserve. The empty partition is included.
-/
theorem partition_composition_reserve_le {n R : ℕ} (p : OrderedFinpartition n)
    (hR : 1 ≤ R) :
    (p.length - R) + ∑ i, (p.partSize i - R) ≤ n - R := by
  by_cases hp : p.length ≤ R
  · simpa only [Nat.sub_eq_zero_of_le hp, zero_add] using partition_sub_reserve_le p R
  · have hsum : (∑ i, (p.partSize i - R)) ≤ ∑ i, (p.partSize i - 1) :=
      Finset.sum_le_sum (fun _ _ ↦ Nat.sub_le_sub_left hR _)
    have htotal := FlowForcing.sum_partSize_sub_one_add_length p
    omega

/-- Multiplying a finite list of nonnegative derivative bounds spends its
total order once. The constants are the product of the supplied constants,
and are independent of the scale (`app:ch_regular_base:eq:joint-primitive-product`).
-/
theorem finite_product_reserve_bound {ι : Type*} (s : Finset ι)
    (j : ι → ℕ) (a C : ι → ℝ) {T : ℝ} (hT : 1 ≤ T) (R : ℕ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hC : ∀ i ∈ s, 0 ≤ C i)
    (hbound : ∀ i ∈ s, a i ≤ C i * T ^ (j i - R)) :
    (∏ i ∈ s, a i) ≤ (∏ i ∈ s, C i) * T ^ ((∑ i ∈ s, j i) - R) := by
  calc
    _ ≤ ∏ i ∈ s, C i * T ^ (j i - R) := Finset.prod_le_prod₀ ha hbound
    _ = (∏ i ∈ s, C i) * T ^ (∑ i ∈ s, (j i - R)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hT (sum_sub_reserve_le s j R)) (Finset.prod_nonneg hC)

end JanetCartan.DerivativeBounds
