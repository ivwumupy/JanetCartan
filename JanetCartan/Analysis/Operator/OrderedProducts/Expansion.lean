module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.Basic

/-!
# Ordered Leibniz expansions

Combinatorics for `app:ch_regular_base:lem:ordered-products` and
`app:ch_regular_base:eq:joint-primitive-product`. Lists retain the literal order
of factors, even when their values do not commute. Repeated Leibniz terms are
retained with multiplicity, so no multinomial coefficients are suppressed.
-/

@[expose] public section

namespace JanetCartan.OrderedProducts

variable {ι A : Type*}

/-- A derivative monomial records the primitive index and derivative order of
each factor, in the order required by `app:ch_regular_base:eq:joint-primitive-product`. -/
abbrev Monomial (ι : Type*) := List (ι × ℕ)

/-- All choices of one factor to differentiate in a literal ordered product. -/
def differentiate : Monomial ι → List (Monomial ι)
  | [] => []
  | (i, j) :: l => ((i, j + 1) :: l) :: (differentiate l).map ((i, j) :: ·)

/-- The complete order-`r` Leibniz expansion, counting multiplicities. -/
def expansion : ℕ → Monomial ι → List (Monomial ι)
  | 0, l => [l]
  | r + 1, l => (expansion r l).flatMap differentiate

/-- Total derivative order, across every factor of a complete monomial. -/
def totalOrder (l : Monomial ι) : ℕ := (l.map Prod.snd).sum

/-- The joint excess over the primitive baselines in
`app:ch_regular_base:eq:joint-primitive-product`. Natural subtraction is positive part. -/
def excessOrder (b : ι → ℕ) (l : Monomial ι) : ℕ :=
  (l.map fun p => p.2 - b p.1).sum

/-- Evaluation uses `List.prod`, requiring no commutativity of the factors. -/
def evaluate [Monoid A] (a : ι → ℕ → A) (l : Monomial ι) : A :=
  (l.map fun p => a p.1 p.2).prod

/-- One Leibniz step preserves all primitive indices in their literal order. -/
theorem indices_differentiate {l m : Monomial ι} (hm : m ∈ differentiate l) :
    m.map Prod.fst = l.map Prod.fst := by
  induction l generalizing m with
  | nil => simp [differentiate] at hm
  | cons p l ih =>
    rcases p with ⟨i, j⟩
    simp only [differentiate, List.mem_cons, List.mem_map] at hm
    rcases hm with rfl | ⟨m, hm, rfl⟩
    · rfl
    · simp [ih hm]

/-- Each Leibniz step adds exactly one to the sum of derivative orders. -/
theorem totalOrder_differentiate {l m : Monomial ι} (hm : m ∈ differentiate l) :
    totalOrder m = totalOrder l + 1 := by
  induction l generalizing m with
  | nil => simp [differentiate] at hm
  | cons p l ih =>
    rcases p with ⟨i, j⟩
    simp only [differentiate, List.mem_cons, List.mem_map] at hm
    rcases hm with rfl | ⟨m, hm, rfl⟩
    · simp [totalOrder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simpa [totalOrder, Nat.add_assoc] using congrArg (j + ·) (ih hm)

/-- Differentiation increases the joint excess budget by at most one. -/
theorem excessOrder_differentiate (b : ι → ℕ) {l m : Monomial ι}
    (hm : m ∈ differentiate l) : excessOrder b m ≤ excessOrder b l + 1 := by
  induction l generalizing m with
  | nil => simp [differentiate] at hm
  | cons p l ih =>
    rcases p with ⟨i, j⟩
    simp only [differentiate, List.mem_cons, List.mem_map] at hm
    rcases hm with rfl | ⟨m, hm, rfl⟩
    · simp only [excessOrder, List.map_cons, List.sum_cons]
      omega
    · have := ih hm
      simp only [excessOrder, List.map_cons, List.sum_cons] at *
      omega

/-- No reordering occurs anywhere in the full Leibniz expansion. -/
theorem indices_expansion (r : ℕ) {l m : Monomial ι} (hm : m ∈ expansion r l) :
    m.map Prod.fst = l.map Prod.fst := by
  induction r generalizing m with
  | zero => simp only [expansion, List.mem_singleton] at hm; subst m; simp
  | succ r ih =>
    obtain ⟨k, hk, hm⟩ := List.mem_flatMap.mp hm
    exact (indices_differentiate hm).trans (ih hk)

/-- Exact global derivative budget for every term, rather than a separate
order-`r` allowance for each factor. -/
theorem totalOrder_expansion (r : ℕ) {l m : Monomial ι} (hm : m ∈ expansion r l) :
    totalOrder m = totalOrder l + r := by
  induction r generalizing m with
  | zero => simp only [expansion, List.mem_singleton] at hm; subst m; simp
  | succ r ih =>
    obtain ⟨k, hk, hm⟩ := List.mem_flatMap.mp hm
    rw [totalOrder_differentiate hm, ih hk, Nat.add_assoc]

/-- Truncated derivative budgets propagate through complete ordered products
(`app:ch_regular_base:eq:joint-primitive-product`). -/
theorem excessOrder_expansion (b : ι → ℕ) (r : ℕ) {l m : Monomial ι}
    (hm : m ∈ expansion r l) : excessOrder b m ≤ excessOrder b l + r := by
  induction r generalizing m with
  | zero => simp only [expansion, List.mem_singleton] at hm; subst m; simp
  | succ r ih =>
    obtain ⟨k, hk, hm⟩ := List.mem_flatMap.mp hm
    have := excessOrder_differentiate b hm
    have := ih hk
    omega

/-- Every step has exactly as many terms as there are factors. -/
theorem length_differentiate (l : Monomial ι) : (differentiate l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => cases p; simp [differentiate, ih]

/-- Differentiation preserves the number of factors in every term. -/
theorem length_term_expansion (r : ℕ) {l m : Monomial ι}
    (hm : m ∈ expansion r l) : m.length = l.length := by
  simpa using congrArg List.length (indices_expansion r hm)

/-- A product with `n` factors has exactly `n^r` terms before collecting
equal monomials. This provides a fixed constant for the tame norm bound. -/
theorem length_expansion (r : ℕ) (l : Monomial ι) :
    (expansion r l).length = l.length ^ r := by
  induction r with
  | zero => simp [expansion]
  | succ r ih =>
    rw [expansion, List.length_flatMap]
    have hmap : ((expansion r l).map fun m => (differentiate m).length) =
        (expansion r l).map (fun _ => l.length) :=
      List.map_congr_left fun m hm => (length_differentiate m).trans
        (length_term_expansion r hm)
    rw [hmap, List.map_const', List.sum_replicate, nsmul_eq_mul, ih, pow_succ]
    simp

section Semiring

variable [Semiring A] (D : A →+ A)
  (hD1 : D 1 = 0) (hDmul : ∀ x y, D (x * y) = D x * y + x * D y)
  (a : ι → ℕ → A) (ha : ∀ i j, D (a i j) = a i (j + 1))

include hD1 hDmul ha

/-- The exact noncommutative Leibniz rule. The hypotheses on `D` are the
additive and product rules; no commutation of operators is assumed. -/
theorem evaluate_differentiate (l : Monomial ι) :
    D (evaluate a l) = ((differentiate l).map (evaluate a)).sum := by
  induction l with
  | nil => simpa [evaluate, differentiate] using hD1
  | cons p l ih =>
    rcases p with ⟨i, j⟩
    simp only [evaluate, List.map_cons, List.prod_cons] at ih ⊢
    rw [hDmul, ha]
    simp only [differentiate, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def, evaluate, List.map_cons, List.prod_cons]
    rw [List.sum_map_mul_left]
    rw [ih]
    rfl

/-- Exact finite expansion of the iterated derivation of an ordered product.
This algebraic statement applies to noncommuting operator-valued factors once
the derivative's additive and Leibniz rules are supplied. -/
theorem iterate_evaluate (r : ℕ) (l : Monomial ι) :
    D^[r] (evaluate a l) = ((expansion r l).map (evaluate a)).sum := by
  induction r with
  | zero => simp [expansion]
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, map_list_sum]
    simp only [List.map_map, Function.comp_def]
    simp only [expansion, List.map_flatMap]
    induction expansion r l with
    | nil => simp
    | cons m ms ihms =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.sum_append]
      rw [evaluate_differentiate D hD1 hDmul a ha, ihms]

end Semiring

section NormedRing

variable [NormedRing A]

/-- Norm domination for a nonempty ordered product, valid also for the
Frobenius matrix norm where the identity need not have norm one. -/
theorem norm_evaluate_le (a : ι → ℕ → A) {l : Monomial ι} (hl : l ≠ []) :
    ‖evaluate a l‖ ≤ (l.map fun p => ‖a p.1 p.2‖).prod := by
  simpa [evaluate, List.map_map, Function.comp_def] using
    (List.norm_prod_le' (by simpa using hl) :
      ‖(l.map fun p => a p.1 p.2).prod‖ ≤ _)

/-- Triangle inequality and submultiplicativity for finitely many ordered
monomials. The scalar products on the right are the input to `Norm.JointBudget`. -/
theorem norm_sum_evaluate_le (a : ι → ℕ → A) (terms : List (Monomial ι))
    (hne : ∀ m ∈ terms, m ≠ []) :
    ‖(terms.map (evaluate a)).sum‖ ≤
      (terms.map fun m => (m.map fun p => ‖a p.1 p.2‖).prod).sum := by
  induction terms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_evaluate_le a (hne m (by simp)))
      (ih fun k hk => hne k (by simp [hk])))

/-- Norm estimate for the complete iterated Leibniz expansion. Together with
`excessOrder_expansion`, this retains the sum of orders across all factors;
scalar interpolation can subsequently be applied once to each complete term. -/
theorem norm_iterate_evaluate_le (D : A →+ A) (hD1 : D 1 = 0)
    (hDmul : ∀ x y, D (x * y) = D x * y + x * D y)
    (a : ι → ℕ → A) (ha : ∀ i j, D (a i j) = a i (j + 1))
    (r : ℕ) {l : Monomial ι} (hl : l ≠ []) :
    ‖D^[r] (evaluate a l)‖ ≤
      ((expansion r l).map fun m => (m.map fun p => ‖a p.1 p.2‖).prod).sum := by
  rw [iterate_evaluate D hD1 hDmul a ha]
  apply norm_sum_evaluate_le
  intro m hm he
  have hlen := length_term_expansion r hm
  rw [he, List.length_nil] at hlen
  exact hl (List.length_eq_zero_iff.mp hlen.symm)

end NormedRing

end JanetCartan.OrderedProducts
