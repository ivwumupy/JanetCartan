module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Calculus

/-!
# Primitive expansions on open neighborhoods

Local Leibniz expansions, with the same counts as the global version, for
Step 3 of `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F G : FullAmplitude n r}
variable {U : Set (Point n)}

/-- Only primitive regularity on `U` is required. The actual phase and its
inverse gap on the carrier produce this hypothesis; no branch bound is a field.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
structure SmoothPrimitivesOn (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (U : Set (Point n)) : Prop where
  amplitude : ∀ p ∈ U, ContDiffAt ℝ ∞ (uncurry A) p
  scalar : ∀ a p, p ∈ U → ContDiffAt ℝ ∞ (uncurry (scalarPrimitive S a)) p

/-- Primitive monomials are smooth locally, with both positions and covectors.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
theorem term_contDiffAt (h : SmoothPrimitivesOn S A U) (t : Term n)
    {p : Point n} (hp : p ∈ U) : ContDiffAt ℝ ∞ (uncurry (t.value S A)) p := by
  induction t with
  | amplitude w => exact contDiffAt_jet (h.amplitude p hp) w
  | factor a w t ih => exact (contDiffAt_jet (h.scalar a p hp) w).smul ih

private theorem sum_contDiffAt (l : List (FullAmplitude n r)) {p : Point n}
    (h : ∀ f ∈ l, ContDiffAt ℝ ∞ (uncurry f) p) :
    ContDiffAt ℝ ∞ (uncurry l.sum) p := by
  induction l with
  | nil => exact contDiffAt_const
  | cons f l ih => exact (h f (by simp)).add (ih (fun g hg => h g (by simp [hg])))

private theorem derivative_sum_at (c : Coordinate n) (l : List (FullAmplitude n r))
    {p : Point n} (h : ∀ f ∈ l, ContDiffAt ℝ ∞ (uncurry f) p) :
    uncurry (derivative c l.sum) p = uncurry (l.map (derivative c)).sum p := by
  induction l with
  | nil => simp [derivative_zero]
  | cons f l ih =>
    have hl : ∀ g ∈ l, ContDiffAt ℝ ∞ (uncurry g) p := fun g hg => h g (by simp [hg])
    simp only [List.sum_cons, List.map_cons]
    rw [derivative_add_at c (sliceDifferentiableAt_of_contDiffAt (h f (by simp)))
      (sliceDifferentiableAt_of_contDiffAt (sum_contDiffAt l hl))]
    change _ + uncurry (derivative c l.sum) p = _ + uncurry (l.map (derivative c)).sum p
    rw [ih hl]

/-- The actual local Leibniz expansion, including inverse derivatives.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem term_derivative_value (h : SmoothPrimitivesOn S A U) (c : Coordinate n)
    (t : Term n) {p : Point n} (hp : p ∈ U) :
    uncurry (derivative c (t.value S A)) p =
      uncurry ((t.differentiate c).map (Term.value S A)).sum p := by
  induction t with
  | amplitude w => simp [Term.value, Term.differentiate]
  | factor a w t ih =>
    rw [Term.value, derivative_multiply_at c
      (sliceDifferentiableAt_of_contDiffAt (contDiffAt_jet (h.scalar a p hp) w))
      (sliceDifferentiableAt_of_contDiffAt (term_contDiffAt h t hp))]
    have hv : (((t.differentiate c).map (.factor a w)).map (Term.value S A)).sum =
        multiply (jet w (scalarPrimitive S a)) ((t.differentiate c).map (Term.value S A)).sum := by
      simp only [multiply_sum, List.map_map]; rfl
    simp only [Term.differentiate, List.map_cons, List.sum_cons]
    rw [hv]
    change _ + (uncurry (jet w (scalarPrimitive S a)) p) • uncurry (derivative c (t.value S A)) p =
      _ + (uncurry (jet w (scalarPrimitive S a)) p) • uncurry ((t.differentiate c).map (Term.value S A)).sum p
    rw [ih]
    rfl

/-- Equality on `U` with bounded order, multiplicity and factor count. This is
proved for the actual branches below, not assumed as primitive data.
Source: the uniform constant in `app:ch_regular_base:eq:fio-input`. -/
def BoundedExpansionOn (S : Euclidean n → Euclidean n → ℝ)
    (A F : FullAmplitude n r) (U : Set (Point n)) (b N m : ℕ) : Prop :=
  ∃ ts : List (Term n), Set.EqOn (uncurry F) (uncurry (ts.map (Term.value S A)).sum) U ∧
    ts.length ≤ N ∧ ∀ t ∈ ts, t.order ≤ b ∧ t.orders.length ≤ m

/-- Initial local expansion with all masks in the amplitude (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansionOn.amplitude : BoundedExpansionOn S A A U 0 1 1 :=
  ⟨[.amplitude []], by simpa [Term.value] using Set.eqOn_refl (uncurry A) U, by simp, by simp [Term.order, Term.orders]⟩

/-- Enlarge numerical bounds without changing the local equality (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansionOn.mono {b N m b' N' m' : ℕ}
    (h : BoundedExpansionOn S A F U b N m) (hb : b ≤ b') (hN : N ≤ N') (hm : m ≤ m') :
    BoundedExpansionOn S A F U b' N' m' := by
  obtain ⟨ts, he, hn, ht⟩ := h
  exact ⟨ts, he, hn.trans hN, fun t h => ⟨(ht t h).1.trans hb, (ht t h).2.trans hm⟩⟩

/-- Local expansions add with their multiplicities (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansionOn.add {b N M m : ℕ}
    (hF : BoundedExpansionOn S A F U b N m) (hG : BoundedExpansionOn S A G U b M m) :
    BoundedExpansionOn S A (F + G) U b (N + M) m := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  obtain ⟨us, hf, hm, hu⟩ := hG
  refine ⟨ts ++ us, ?_, by simpa using Nat.add_le_add hn hm,
    by simpa using fun t h => h.elim (ht t) (hu t)⟩
  intro p hp
  simpa [uncurry] using congrArg₂ (· + ·) (he hp) (hf hp)

/-- Finite local sums have the same uniform count as global sums (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansionOn.sum {ι : Type*} (s : Finset ι)
    (F : ι → FullAmplitude n r) (b N m : ℕ)
    (h : ∀ i ∈ s, BoundedExpansionOn S A (F i) U b N m) :
    BoundedExpansionOn S A (∑ i ∈ s, F i) U b (s.card * N) m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simpa using Set.eqOn_refl (uncurry (0 : FullAmplitude n r)) U, by simp, by simp⟩
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul,
      Nat.add_comm] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- Multiplication by the actual mixed or inverse entry adds one factor.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem BoundedExpansionOn.multiply {b N m : ℕ}
    (hF : BoundedExpansionOn S A F U b N m) (a : ScalarIndex n) :
    BoundedExpansionOn S A (multiply (scalarPrimitive S a) F) U b N (m + 1) := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  refine ⟨ts.map (.factor a []), ?_, by simpa using hn, ?_⟩
  · intro p hp
    have hv : ((ts.map (.factor a [])).map (Term.value S A)).sum =
        FullAmplitudePrimitiveBudget.multiply (scalarPrimitive S a) (ts.map (Term.value S A)).sum := by
      simp only [multiply_sum, List.map_map]; rfl
    rw [hv]
    exact congrArg (uncurry (scalarPrimitive S a) p • ·) (he hp)
  · intro t hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    simpa [Term.order, Term.orders] using ht u hu

private theorem sum_eval_map {ι : Type*} (l : List ι) (f : ι → FullAmplitude n r)
    (p : Point n) : uncurry (l.map f).sum p = (l.map (fun t => uncurry (f t) p)).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simpa only [List.map_cons, List.sum_cons, uncurry, Pi.add_apply] using congrArg (uncurry (f t) p + ·) ih

/-- One actual derivative of a neighborhood expansion costs one order and at
most one term per factor. Source: Step 3 of the actual calculus.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem BoundedExpansionOn.derivative (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    {b N m : ℕ} (hF : BoundedExpansionOn S A F U b N m) (c : Coordinate n) :
    BoundedExpansionOn S A (derivative c F) U (b + 1) (N * m) m := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  refine ⟨ts.flatMap (Term.differentiate c), ?_, ?_, ?_⟩
  · intro p hp
    rw [derivative_eqOn hU he c hp, derivative_sum_at c _ (by
      intro f hf
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
      exact term_contDiffAt h t hp)]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    simp only [sum_eval_map]
    congr 1
    apply List.map_congr_left
    intro t _
    exact term_derivative_value h c t hp
  · have hlen : (ts.flatMap (Term.differentiate c)).length ≤ ts.length * m := by
      clear he
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

/-- A low joint word spends only its length in the total derivative budget.
Source: the low operator reserve preceding `app:ch_regular_base:eq:fio-input`. -/
theorem BoundedExpansionOn.jet (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    {b N m : ℕ} (hF : BoundedExpansionOn S A F U b N m) (w : List (Coordinate n)) :
    BoundedExpansionOn S A (jet w F) U (b + w.length) (N * m ^ w.length) m := by
  induction w with
  | nil => simpa using hF
  | cons c w ih =>
    simpa [Nat.add_assoc, pow_succ, Nat.mul_assoc] using ih.derivative hU h c

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
