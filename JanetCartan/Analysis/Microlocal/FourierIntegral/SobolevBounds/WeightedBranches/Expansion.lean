module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.WeightedJets

/-!
# Frequency counts in local primitive expansions

Local Leibniz expansions, with the same counts as the global version, for
Step 3 of `app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
open Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F G : FullAmplitude n r}
variable {U : Set (Point n)}

open FirstOutputJets

/-- Total covector order of a primitive monomial. It is conserved by the
physical transfer and split by Leibniz differentiation. Source:
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
def Term.frequencyOrder : Term n → ℕ
  | .amplitude w => FirstOutputJets.frequencyOrder w
  | .factor _ w t => FirstOutputJets.frequencyOrder w + t.frequencyOrder

/-- Each Leibniz term receives exactly the new covector slot, if any.
Source: the weighted low reserve in Step 3 of the actual calculus. -/
theorem Term.frequencyOrder_differentiate (c : Coordinate n) {t u : Term n}
    (hu : u ∈ t.differentiate c) :
    u.frequencyOrder = t.frequencyOrder + FirstOutputJets.frequencyOrder [c] := by
  induction t generalizing u with
  | amplitude w =>
    simp only [Term.differentiate, List.mem_singleton] at hu
    subst u
    simp [Term.frequencyOrder, FirstOutputJets.frequencyOrder, List.countP_cons, Nat.add_comm]
  | factor a w t ih =>
    simp only [Term.differentiate, List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨u, hu, rfl⟩
    · simp [Term.frequencyOrder, FirstOutputJets.frequencyOrder, List.countP_cons, Nat.add_comm,
        Nat.add_left_comm]
    · simp [Term.frequencyOrder, ih hu, Nat.add_assoc]

namespace Local.Weighted

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

/-- Equality on `U` with bounded order, multiplicity and factor count. This is
proved for the actual branches below, not assumed as primitive data.
Source: the uniform constant in `app:ch_regular_base:eq:fio-input`. -/
def WeightedExpansionOn (S : Euclidean n → Euclidean n → ℝ)
    (A F : FullAmplitude n r) (U : Set (Point n)) (b N m f : ℕ) : Prop :=
  ∃ ts : List (Term n), Set.EqOn (uncurry F) (uncurry (ts.map (Term.value S A)).sum) U ∧
    ts.length ≤ N ∧ ∀ t ∈ ts, t.order ≤ b ∧ t.orders.length ≤ m ∧ t.frequencyOrder = f

/-- Initial local expansion with all masks in the amplitude (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem WeightedExpansionOn.amplitude : WeightedExpansionOn S A A U 0 1 1 0 :=
  ⟨[.amplitude []], by simpa [Term.value] using Set.eqOn_refl (uncurry A) U, by simp, by simp [Term.order, Term.orders, Term.frequencyOrder, FirstOutputJets.frequencyOrder]⟩

/-- Enlarge numerical bounds without changing the local equality (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem WeightedExpansionOn.mono {b N m b' N' m' f : ℕ}
    (h : WeightedExpansionOn S A F U b N m f) (hb : b ≤ b') (hN : N ≤ N') (hm : m ≤ m') :
    WeightedExpansionOn S A F U b' N' m' f := by
  obtain ⟨ts, he, hn, ht⟩ := h
  exact ⟨ts, he, hn.trans hN, fun t h => ⟨(ht t h).1.trans hb, (ht t h).2.1.trans hm, (ht t h).2.2⟩⟩

/-- Local expansions add with their multiplicities (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem WeightedExpansionOn.add {b N M m f : ℕ}
    (hF : WeightedExpansionOn S A F U b N m f) (hG : WeightedExpansionOn S A G U b M m f) :
    WeightedExpansionOn S A (F + G) U b (N + M) m f := by
  obtain ⟨ts, he, hn, ht⟩ := hF
  obtain ⟨us, hf, hm, hu⟩ := hG
  refine ⟨ts ++ us, ?_, by simpa using Nat.add_le_add hn hm,
    by simpa using fun t h => h.elim (ht t) (hu t)⟩
  intro p hp
  simpa [uncurry] using congrArg₂ (· + ·) (he hp) (hf hp)

/-- Finite local sums have the same uniform count as global sums (Step 3).
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem WeightedExpansionOn.sum {ι : Type*} (s : Finset ι)
    (F : ι → FullAmplitude n r) (b N m f : ℕ)
    (h : ∀ i ∈ s, WeightedExpansionOn S A (F i) U b N m f) :
    WeightedExpansionOn S A (∑ i ∈ s, F i) U b (s.card * N) m f := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simpa using Set.eqOn_refl (uncurry (0 : FullAmplitude n r)) U, by simp, by simp⟩
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul,
      Nat.add_comm] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- Multiplication by the actual mixed or inverse entry adds one factor.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem WeightedExpansionOn.multiply {b N m f : ℕ}
    (hF : WeightedExpansionOn S A F U b N m f) (a : ScalarIndex n) :
    WeightedExpansionOn S A (multiply (scalarPrimitive S a) F) U b N (m + 1) f := by
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
    simpa [Term.order, Term.orders, Term.frequencyOrder, FirstOutputJets.frequencyOrder] using ht u hu

private theorem sum_eval_map {ι : Type*} (l : List ι) (f : ι → FullAmplitude n r)
    (p : Point n) : uncurry (l.map f).sum p = (l.map (fun t => uncurry (f t) p)).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simpa only [List.map_cons, List.sum_cons, uncurry, Pi.add_apply] using congrArg (uncurry (f t) p + ·) ih

/-- One actual derivative of a neighborhood expansion costs one order and at
most one term per factor. Source: Step 3 of the actual calculus.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem WeightedExpansionOn.derivative (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    {b N m f : ℕ} (hF : WeightedExpansionOn S A F U b N m f) (c : Coordinate n) :
    WeightedExpansionOn S A (derivative c F) U (b + 1) (N * m) m (f + FirstOutputJets.frequencyOrder [c]) := by
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
    rw [Term.order_differentiate c hu, Term.orders_length_differentiate c hu, Term.frequencyOrder_differentiate c hu]
    exact ⟨Nat.add_le_add_right (ht t hts).1 1, (ht t hts).2.1, by rw [(ht t hts).2.2]⟩

/-- A low joint word spends only its length in the total derivative budget.
Source: the low operator reserve preceding `app:ch_regular_base:eq:fio-input`. -/
theorem WeightedExpansionOn.jet (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    {b N m f : ℕ} (hF : WeightedExpansionOn S A F U b N m f) (w : List (Coordinate n)) :
    WeightedExpansionOn S A (jet w F) U (b + w.length) (N * m ^ w.length) m (f + FirstOutputJets.frequencyOrder w) := by
  induction w with
  | nil => simpa [FirstOutputJets.frequencyOrder] using hF
  | cons c w ih =>
    simpa [FirstOutputJets.frequencyOrder, List.countP_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, pow_succ, Nat.mul_assoc] using ih.derivative hU h c

end Local.Weighted
end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
