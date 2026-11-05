module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget

/-!
# Uniform sizes of the concrete graph primitive expansions

The constants in `app:ch_regular_base:eq:fio-input` must precede the high
primitive bounds. The derivative budget alone does not bound the number of
monomials or undifferentiated factors. This leaf supplies both bounds for the
actual forward and reverse branches, for use in the low operator seminorm.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F G : FullAmplitude n r}

/-- Leibniz differentiation produces one term per primitive factor.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.length_differentiate (t : Term n) (c : Coordinate n) :
    (t.differentiate c).length = t.orders.length := by
  induction t with
  | amplitude w => rfl
  | factor a w t ih => simp [differentiate, orders, ih]

/-- Differentiation changes orders but never the number of primitive factors.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.orders_length_differentiate (c : Coordinate n) {t u : Term n}
    (hu : u ∈ t.differentiate c) : u.orders.length = t.orders.length := by
  induction t generalizing u with
  | amplitude w =>
    simp only [differentiate, List.mem_singleton] at hu
    subst u
    rfl
  | factor a w t ih =>
    simp only [differentiate, List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨u, hu, rfl⟩
    · rfl
    · simp only [orders, List.length_cons, ih hu]

/-- A proved finite primitive representation with bounds on total order,
number of summands, and number of factors. This predicate will be proved for
the concrete transfer branches, not postulated as an analytic input.
Source: the uniform constant in `app:ch_regular_base:eq:fio-input`. -/
def BoundedExpansion (S : Euclidean n → Euclidean n → ℝ)
    (A F : FullAmplitude n r) (b N m : ℕ) : Prop :=
  ∃ ts : List (Term n), F = (ts.map (Term.value S A)).sum ∧ ts.length ≤ N ∧
    ∀ t ∈ ts, t.order ≤ b ∧ t.orders.length ≤ m

/-- The full initial amplitude has one term and one factor.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem BoundedExpansion.amplitude : BoundedExpansion S A A 0 1 1 :=
  ⟨[.amplitude []], by simp [Term.value], by simp, by simp [Term.order, Term.orders]⟩

/-- Enlargement of numerical expansion bounds.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansion.mono {b N m b' N' m' : ℕ}
    (h : BoundedExpansion S A F b N m) (hb : b ≤ b') (hN : N ≤ N') (hm : m ≤ m') :
    BoundedExpansion S A F b' N' m' := by
  obtain ⟨ts, he, hn, ht⟩ := h
  exact ⟨ts, he, hn.trans hN, fun t h => ⟨(ht t h).1.trans hb, (ht t h).2.trans hm⟩⟩

/-- Addition retains multiplicities and adds the term counts.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansion.add {b N M m : ℕ}
    (hF : BoundedExpansion S A F b N m) (hG : BoundedExpansion S A G b M m) :
    BoundedExpansion S A (F + G) b (N + M) m := by
  obtain ⟨ts, rfl, hn, ht⟩ := hF
  obtain ⟨us, rfl, hm, hu⟩ := hG
  exact ⟨ts ++ us, by simp, by simpa using Nat.add_le_add hn hm,
    by simpa using fun t h => h.elim (ht t) (hu t)⟩

/-- A finite coordinate sum multiplies the uniform term count by its size.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansion.sum {ι : Type*} (s : Finset ι)
    (F : ι → FullAmplitude n r) (b N m : ℕ)
    (h : ∀ i ∈ s, BoundedExpansion S A (F i) b N m) :
    BoundedExpansion S A (∑ i ∈ s, F i) b (s.card * N) m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp⟩
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul,
      Nat.add_comm] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- An undifferentiated mixed or inverse entry adds one factor.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem BoundedExpansion.multiply {b N m : ℕ}
    (hF : BoundedExpansion S A F b N m) (a : ScalarIndex n) :
    BoundedExpansion S A (multiply (scalarPrimitive S a) F) b N (m + 1) := by
  obtain ⟨ts, rfl, hn, ht⟩ := hF
  refine ⟨ts.map (.factor a []), ?_, by simpa using hn, ?_⟩
  · rw [multiply_sum]
    simp only [List.map_map]
    rfl
  · intro t hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    simpa [Term.order, Term.orders] using ht u hu

/-- One joint derivative costs one order and at most `m` terms per term.
Source: the fixed low seminorm reserve in Step 3 of the actual calculus. -/
theorem BoundedExpansion.derivative (h : SmoothPrimitives S A) {b N m : ℕ}
    (hF : BoundedExpansion S A F b N m) (c : Coordinate n) :
    BoundedExpansion S A (derivative c F) (b + 1) (N * m) m := by
  obtain ⟨ts, rfl, hn, ht⟩ := hF
  refine ⟨ts.flatMap (Term.differentiate c), ?_, ?_, ?_⟩
  · rw [derivative_sum c _ (by
      intro f hf
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
      exact t.differentiable h)]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    exact t.derivative_value h c
  · have hlen : (ts.flatMap (Term.differentiate c)).length ≤ ts.length * m := by
      induction ts with
      | nil => simp
      | cons t ts ih =>
        have ht' := ht t (by simp)
        have hi := ih (by simpa only [List.length_cons] using (Nat.le_trans (Nat.le_succ ts.length) hn)) (fun u hu => ht u (by simp [hu]))
        simp only [List.flatMap_cons, List.length_append, Term.length_differentiate,
          List.length_cons, Nat.add_mul, one_mul]
        omega
    exact hlen.trans (Nat.mul_le_mul_right m hn)
  · intro u hu
    obtain ⟨t, hts, hu⟩ := List.mem_flatMap.mp hu
    rw [Term.order_differentiate c hu, Term.orders_length_differentiate c hu]
    exact ⟨Nat.add_le_add_right (ht t hts).1 1, (ht t hts).2⟩

/-- An additional joint word spends its length in the derivative budget,
while its term count depends only on the fixed factor count.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansion.jet (h : SmoothPrimitives S A) {b N m : ℕ}
    (hF : BoundedExpansion S A F b N m) (w : List (Coordinate n)) :
    BoundedExpansion S A (jet w F) (b + w.length) (N * m ^ w.length) m := by
  induction w with
  | nil => simpa using hF
  | cons c w ih =>
    simpa [Nat.add_assoc, pow_succ, Nat.mul_assoc] using ih.derivative h c

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
