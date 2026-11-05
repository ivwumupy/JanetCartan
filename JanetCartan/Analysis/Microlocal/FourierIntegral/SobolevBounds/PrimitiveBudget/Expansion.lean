module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget.Coordinates
public import JanetCartan.Analysis.Operator.OrderedProducts.OneHigh

/-!
# Primitive monomials for the actual graph branches

The finite Leibniz expansion in Step 3 of `app:ch_regular_base:thm:actual-calculus`.
Every term contains scalar jets of the actual mixed matrix or its actual inverse,
and exactly one matrix jet of the complete amplitude. No symbolic derivative
rule is an input: the expansion is proved using actual partial derivatives.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
variable {n r : ℕ}

/-- `false` selects the actual mixed matrix and `true` its actual inverse.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
abbrev ScalarIndex (n : ℕ) := Bool × Fin n × Fin n

/-- The scalar primitives in Step 3; the dummy second position is retained.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def scalarPrimitive (S : Euclidean n → Euclidean n → ℝ) (a : ScalarIndex n) : Field n ℂ :=
  fun x _ η => if a.1 then ((mixedPhaseMatrix S x η)⁻¹ a.2.1 a.2.2 : ℂ)
    else (mixedPhaseMatrix S x η a.2.1 a.2.2 : ℂ)

/-- A scalar product ending in exactly one complete matrix-amplitude jet.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
inductive Term (n : ℕ) where
  | amplitude (w : List (Coordinate n))
  | factor (a : ScalarIndex n) (w : List (Coordinate n)) (tail : Term n)

/-- Literal evaluation, retaining all masks inside `A`. For reverse branches,
`A` is the already conjugate-transposed amplitude.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def Term.value (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) :
    Term n → FullAmplitude n r
  | .amplitude w => jet w A
  | .factor a w t => multiply (jet w (scalarPrimitive S a)) (t.value S A)

/-- Total derivative order shared by every factor in the complete term.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def Term.order : Term n → ℕ
  | .amplitude w => w.length
  | .factor _ w t => w.length + t.order

/-- Primitive labels: `none` is the matrix amplitude; scalar entries are `some a`.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def Term.orders : Term n → OrderedProducts.Monomial (Option (ScalarIndex n))
  | .amplitude w => [(none, w.length)]
  | .factor a w t => (some a, w.length) :: t.orders

/-- Identification with the existing total-order API.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.totalOrder_orders (t : Term n) : OrderedProducts.totalOrder t.orders = t.order := by
  induction t with
  | amplitude w => simp [orders, order, OrderedProducts.totalOrder]
  | factor a w t ih => simpa [orders, order, OrderedProducts.totalOrder] using congrArg (w.length + ·) ih

/-- One Leibniz step differentiates each primitive in turn, with multiplicity.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def Term.differentiate (c : Coordinate n) : Term n → List (Term n)
  | .amplitude w => [.amplitude (c :: w)]
  | .factor a w t => .factor a (c :: w) t :: (t.differentiate c).map (.factor a w)

/-- Each summand spends exactly one new joint derivative.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.order_differentiate (c : Coordinate n) {t u : Term n}
    (hu : u ∈ t.differentiate c) : u.order = t.order + 1 := by
  induction t generalizing u with
  | amplitude w =>
    simp only [differentiate, List.mem_singleton] at hu
    subst u
    simp [order]
  | factor a w t ih =>
    simp only [differentiate, List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨u, hu, rfl⟩
    · simp [order, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp [order, ih hu, Nat.add_assoc]

/-- Actual scalar primitive jets and the complete amplitude are the only
smoothness inputs needed below. Their producers are phase/geometry regularity.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
structure SmoothPrimitives (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r) : Prop where
  amplitude : JetSmooth A
  scalar : ∀ a, JetSmooth (scalarPrimitive S a)

variable {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Products of primitive jets are differentiable in all three slots.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.differentiable (h : SmoothPrimitives S A) (t : Term n) :
    SliceDifferentiable (t.value S A) := by
  induction t with
  | amplitude w => exact h.amplitude w
  | factor a w t ih => exact (h.scalar a w).multiply ih

/-- Multiply a finite sum of full fields without losing any terms.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem multiply_sum (f : Field n ℂ) (l : List (FullAmplitude n r)) :
    multiply f l.sum = (l.map (multiply f)).sum := by
  induction l with
  | nil => funext x y η; simp [multiply]
  | cons g l ih =>
    simp only [List.sum_cons, List.map_cons, ← ih]
    funext x y η
    exact smul_add _ _ _

/-- Pointwise field sums are differentiable when their summands are.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem differentiable_sum (l : List (FullAmplitude n r))
    (h : ∀ f ∈ l, SliceDifferentiable f) : SliceDifferentiable l.sum := by
  induction l with
  | nil => exact SliceDifferentiable.zero
  | cons f l ih =>
    exact (h f (by simp)).add (ih (fun g hg => h g (by simp [hg])))

/-- Differentiate a finite sum using the actual derivative.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_sum (c : Coordinate n) (l : List (FullAmplitude n r))
    (h : ∀ f ∈ l, SliceDifferentiable f) :
    derivative c l.sum = (l.map (derivative c)).sum := by
  induction l with
  | nil => exact derivative_zero c
  | cons f l ih =>
    have hl : ∀ g ∈ l, SliceDifferentiable g := fun g hg => h g (by simp [hg])
    simp only [List.sum_cons, List.map_cons]
    rw [derivative_add c (h f (by simp)) (differentiable_sum l hl), ih hl]

/-- The finite primitive expansion is the actual Leibniz rule, including
inverse derivatives in the reverse remainder.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Term.derivative_value (h : SmoothPrimitives S A) (c : Coordinate n) (t : Term n) :
    derivative c (t.value S A) = ((t.differentiate c).map (Term.value S A)).sum := by
  induction t with
  | amplitude w => simp [value, differentiate]
  | factor a w t ih =>
    rw [value, derivative_multiply c (h.scalar a w) (t.differentiable h), ih, multiply_sum]
    simp only [differentiate, List.map_cons, List.sum_cons, List.map_map, value, jet_cons]
    rfl

/-- A finite sum representation with one shared primitive derivative budget.
This predicate is proved for concrete branches below, never assumed for them.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def Expansion (S : Euclidean n → Euclidean n → ℝ) (A F : FullAmplitude n r) (b : ℕ) : Prop :=
  ∃ ts : List (Term n), F = (ts.map (Term.value S A)).sum ∧ ∀ t ∈ ts, t.order ≤ b

/-- The undifferentiated full amplitude has budget zero.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.amplitude : Expansion S A A 0 :=
  ⟨[.amplitude []], by simp [Term.value], by simp [Term.order]⟩

/-- Enlarging the total budget does not alter the expansion.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.mono {F : FullAmplitude n r} {b d : ℕ}
    (h : Expansion S A F b) (hbd : b ≤ d) : Expansion S A F d := by
  obtain ⟨ts, ht, hb⟩ := h
  exact ⟨ts, ht, fun t ht => (hb t ht).trans hbd⟩

/-- Addition concatenates the finite expansions.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.add {F G : FullAmplitude n r} {b : ℕ}
    (hF : Expansion S A F b) (hG : Expansion S A G b) : Expansion S A (F + G) b := by
  obtain ⟨ts, rfl, ht⟩ := hF
  obtain ⟨us, rfl, hu⟩ := hG
  exact ⟨ts ++ us, by simp, by simpa using fun t h => h.elim (ht t) (hu t)⟩

/-- The empty sum is represented by the empty list.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.zero (b : ℕ) : Expansion S A 0 b := ⟨[], by simp, by simp⟩

/-- Finite sums retain a common budget.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.sum {ι : Type*} (s : Finset ι) (F : ι → FullAmplitude n r) (b : ℕ)
    (h : ∀ i ∈ s, Expansion S A (F i) b) : Expansion S A (∑ i ∈ s, F i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Expansion.zero b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

/-- Multiplication by an undifferentiated matrix/inverse entry costs no derivatives.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.multiply {F : FullAmplitude n r} {b : ℕ}
    (hF : Expansion S A F b) (a : ScalarIndex n) :
    Expansion S A (multiply (scalarPrimitive S a) F) b := by
  obtain ⟨ts, rfl, ht⟩ := hF
  refine ⟨ts.map (.factor a []), ?_, ?_⟩
  · rw [multiply_sum]
    simp only [List.map_map]
    rfl
  · intro t hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    simpa [Term.order] using ht u hu

/-- One actual joint derivative adds one to the shared budget.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.derivative (h : SmoothPrimitives S A) {F : FullAmplitude n r} {b : ℕ}
    (hF : Expansion S A F b) (c : Coordinate n) : Expansion S A (derivative c F) (b + 1) := by
  obtain ⟨ts, rfl, ht⟩ := hF
  refine ⟨ts.flatMap (Term.differentiate c), ?_, ?_⟩
  · rw [derivative_sum c _ (by
      intro f hf
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
      exact t.differentiable h)]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    exact t.derivative_value h c
  · intro u hu
    obtain ⟨t, hts, hu⟩ := List.mem_flatMap.mp hu
    rw [Term.order_differentiate c hu]
    exact Nat.add_le_add_right (ht t hts) 1

/-- An additional joint word adds only its length, including covector derivatives.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem Expansion.jet (h : SmoothPrimitives S A) {F : FullAmplitude n r} {b : ℕ}
    (hF : Expansion S A F b) (w : List (Coordinate n)) : Expansion S A (jet w F) (b + w.length) := by
  induction w with
  | nil => simpa using hF
  | cons c w ih => simpa [Nat.add_assoc] using ih.derivative h c

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
