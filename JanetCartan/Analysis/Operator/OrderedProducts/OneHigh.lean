module

public import JanetCartan.Analysis.Operator.OrderedProducts.Expansion
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget.Algebra

import Mathlib.Algebra.BigOperators.Fin

/-!
# One high norm for complete ordered products

The ordered-matrix conclusion of `app:ch_regular_base:eq:joint-primitive-product`,
and its application to the complete Leibniz expansion. The analytic input is the
precise intermediate-order interpolation estimate for a monotone scalar majorant
of the factor norms. The proof uses `JointBudget.finite_product_le_one_high` once
per complete monomial, with a single budget shared by all its factors.

No commutativity of the underlying factors, nor norm-one identity, is required.
The norm estimates concern nonempty products, so they apply to the Frobenius norm.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.OrderedProducts

variable {ι A : Type*}

/-- List version of `app:ch_regular_base:eq:joint-primitive-product`. Indexing
by positions retains repeated primitives and all scalar multiplicities. The
only analytic premise is the displayed intermediate-order interpolation bound. -/
theorem list_product_le_one_high (I : Finset ι) (q : ι → ℕ → ℝ) (b : ι → ℕ)
    (l : Monomial ι) (W : ℕ) (B K : ℝ)
    (hq : ∀ i ∈ I, ∀ r, 0 ≤ q i r) (hmono : ∀ i ∈ I, Monotone (q i))
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hlow : ∀ i ∈ I, q i (b i) ≤ B)
    (hindex : ∀ p ∈ l, p.1 ∈ I) (hbudget : excessOrder b l ≤ W)
    (hinterp : ∀ i ∈ I, ∀ j, b i < j → j < b i + W →
      q i j ≤ K * q i (b i) ^ (1 - ((j - b i : ℕ) : ℝ) / W) *
        q i (b i + W) ^ (((j - b i : ℕ) : ℝ) / W)) :
    (l.map fun p => q p.1 p.2).prod ≤
      (K * B) ^ l.length * (1 + ∑ i ∈ I, q i (b i + W)) := by
  have hb : ∑ h : Fin l.length, (l[(h : ℕ)].2 - b l[(h : ℕ)].1) ≤ W := by
    simpa only [← List.sum_ofFn,
      List.ofFn_getElem_eq_map l (fun p => p.2 - b p.1), excessOrder] using hbudget
  have h := JointBudget.finite_product_le_one_high I Finset.univ q b
    (fun h : Fin l.length => l[(h : ℕ)].1) (fun h : Fin l.length => l[(h : ℕ)].2)
    W B K hq hmono hB hK hlow (fun h _ => hindex _ (List.getElem_mem _)) hb hinterp
  simpa only [← List.prod_ofFn, List.ofFn_getElem_eq_map l (fun p => q p.1 p.2),
    Finset.card_univ, Fintype.card_fin] using h

variable [NormedRing A]

/-- Ordered noncommutative product estimate from
`app:ch_regular_base:eq:joint-primitive-product`. `q` is a nonnegative monotone
majorant (for example full derivative seminorms); its interpolation estimate is
an explicit input. Each primitive contributes only once to the high sum. -/
theorem norm_evaluate_le_one_high (I : Finset ι) (a : ι → ℕ → A)
    (q : ι → ℕ → ℝ) (b : ι → ℕ) {l : Monomial ι} (hl : l ≠ [])
    (W : ℕ) (B K : ℝ)
    (hnorm : ∀ i ∈ I, ∀ j, ‖a i j‖ ≤ q i j)
    (hmono : ∀ i ∈ I, Monotone (q i))
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hlow : ∀ i ∈ I, q i (b i) ≤ B)
    (hindex : ∀ p ∈ l, p.1 ∈ I) (hbudget : excessOrder b l ≤ W)
    (hinterp : ∀ i ∈ I, ∀ j, b i < j → j < b i + W →
      q i j ≤ K * q i (b i) ^ (1 - ((j - b i : ℕ) : ℝ) / W) *
        q i (b i + W) ^ (((j - b i : ℕ) : ℝ) / W)) :
    ‖evaluate a l‖ ≤ (K * B) ^ l.length * (1 + ∑ i ∈ I, q i (b i + W)) := by
  have hq : ∀ i ∈ I, ∀ j, 0 ≤ q i j :=
    fun i hi j => (norm_nonneg _).trans (hnorm i hi j)
  apply (norm_evaluate_le a hl).trans
  apply le_trans _ (list_product_le_one_high I q b l W B K hq hmono
    hB hK hlow hindex hbudget hinterp)
  have h := Finset.prod_le_prod₀
    (s := (Finset.univ : Finset (Fin l.length)))
    (f := fun h : Fin l.length => ‖a l[(h : ℕ)].1 l[(h : ℕ)].2‖)
    (g := fun h : Fin l.length => q l[(h : ℕ)].1 l[(h : ℕ)].2)
    (fun _ _ => norm_nonneg _)
    (fun h _ => hnorm _ (hindex _ (List.getElem_mem _)) _)
  simpa only [← List.prod_ofFn,
    List.ofFn_getElem_eq_map l (fun p => ‖a p.1 p.2‖),
    List.ofFn_getElem_eq_map l (fun p => q p.1 p.2)] using h

/-- One-high estimate for the full order-`r` ordered Leibniz expansion
(`app:ch_regular_base:eq:joint-primitive-product`). The input budget is the
*sum* of initial excess orders plus `r`; no factor receives a separate budget.
The constant `length^r * (K * B)^length` is independent of all high norms.
Derivative rules, norm domination, and scalar interpolation are explicit inputs. -/
theorem norm_iterate_evaluate_le_one_high (D : A →+ A) (hD1 : D 1 = 0)
    (hDmul : ∀ x y, D (x * y) = D x * y + x * D y)
    (I : Finset ι) (a : ι → ℕ → A) (ha : ∀ i j, D (a i j) = a i (j + 1))
    (q : ι → ℕ → ℝ) (b : ι → ℕ) (r : ℕ) {l : Monomial ι} (hl : l ≠ [])
    (W : ℕ) (B K : ℝ)
    (hnorm : ∀ i ∈ I, ∀ j, ‖a i j‖ ≤ q i j)
    (hmono : ∀ i ∈ I, Monotone (q i))
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hlow : ∀ i ∈ I, q i (b i) ≤ B)
    (hindex : ∀ p ∈ l, p.1 ∈ I) (hbudget : excessOrder b l + r ≤ W)
    (hinterp : ∀ i ∈ I, ∀ j, b i < j → j < b i + W →
      q i j ≤ K * q i (b i) ^ (1 - ((j - b i : ℕ) : ℝ) / W) *
        q i (b i + W) ^ (((j - b i : ℕ) : ℝ) / W)) :
    ‖D^[r] (evaluate a l)‖ ≤
      (l.length : ℝ) ^ r * (K * B) ^ l.length *
        (1 + ∑ i ∈ I, q i (b i + W)) := by
  have hterm (m : Monomial ι) (hm : m ∈ expansion r l) :
      ‖evaluate a m‖ ≤ (K * B) ^ l.length * (1 + ∑ i ∈ I, q i (b i + W)) := by
    have hlen := length_term_expansion r hm
    have hne : m ≠ [] := by
      intro he
      rw [he, List.length_nil] at hlen
      exact hl (List.length_eq_zero_iff.mp hlen.symm)
    have hmi : ∀ p ∈ m, p.1 ∈ I := by
      intro p hp
      have hi : p.1 ∈ l.map Prod.fst := by
        rw [← indices_expansion r hm]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨k, hk, he⟩ := List.mem_map.mp hi
      exact he ▸ hindex k hk
    simpa only [hlen] using norm_evaluate_le_one_high I a q b hne W B K
      hnorm hmono hB hK hlow hmi ((excessOrder_expansion b r hm).trans hbudget) hinterp
  rw [iterate_evaluate D hD1 hDmul a ha]
  apply (norm_multiset_sum_le (↑((expansion r l).map (evaluate a)) : Multiset A)).trans
  have hsum := List.sum_le_sum hterm
  simpa only [Multiset.map_coe, Multiset.sum_coe, List.map_map, Function.comp_def,
    List.map_const', List.sum_replicate, nsmul_eq_mul, length_expansion,
    Nat.cast_pow, mul_assoc] using hsum

end JanetCartan.OrderedProducts
