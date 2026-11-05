module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualTerms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains
public import Mathlib.Data.List.OfFn

/-!
# Ordered words for the complete normalized residual

For `app:ch_regular:lem:finite-chain`, a word records factors in application
order: letter zero acts first. We use `List.ofFn` and its noncommutative product,
not a commutative product or the powers of separate charts. The alphabet is
fixed before the varying operator family. Real compression is performed only
after the complete complex composition.
-/

@[expose] public noncomputable section

namespace JanetCartan.RegularSector.NormalizedResidualWords

open MeasureTheory Realization
open scoped JanetCartan.RegularSector.Realization

/-- A word in application order for `app:ch_regular:lem:finite-chain`.
Its value is `T (w (j-1)) * ... * T (w 0)`; the empty word is the identity. -/
def orderedWord {α A : Type*} [Monoid A] (T : α → A) {j : ℕ}
    (w : Fin j → α) : A := (List.ofFn (fun k ↦ T (w k))).reverse.prod

/-- The zero-length word in `app:ch_regular:eq:finite-observation` retains
the identity, including its nonvanishing angular observation. -/
@[simp] theorem orderedWord_zero {α A : Type*} [Monoid A] (T : α → A)
    (w : Fin 0 → α) : orderedWord T w = 1 := by
  simp [orderedWord]

/-- Prepending the first applied letter leaves it at the right of the
noncommutative composition (`app:ch_regular:lem:finite-chain`). -/
theorem orderedWord_cons {α A : Type*} [Monoid A] (T : α → A)
    {j : ℕ} (a : α) (w : Fin j → α) :
    orderedWord T (Fin.cons a w) = orderedWord T w * T a := by
  simp [orderedWord, List.ofFn_succ]

/-- Appending the last applied letter leaves it at the left of the
noncommutative composition (`app:ch_regular:lem:finite-chain`). -/
theorem orderedWord_succ {α A : Type*} [Monoid A] (T : α → A)
    {j : ℕ} (w : Fin (j+1) → α) :
    orderedWord T w = T (w (Fin.last j)) *
      orderedWord T (fun k ↦ w k.castSucc) := by
  simp only [orderedWord]
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons]

/-- Expand a finite sum power into all ordered words, with repetitions and
mixed letters, for `app:ch_regular:eq:chain-tail`. Mathlib's `Finset.sum_pow`
requires commutativity; this proof uses its tuple equivalence and list product. -/
theorem sum_pow_eq_sum_orderedWord {α A : Type*} [Fintype α] [Semiring A]
    (T : α → A) (j : ℕ) :
    (∑ a, T a) ^ j = ∑ w : Fin j → α, orderedWord T w := by
  classical
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (j+1) ↦ α)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk,
      orderedWord_cons]
    simp only [Finset.sum_mul, Finset.mul_sum]

private theorem adjoint_list_prod {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] (l : List (X →L[ℂ] X)) :
    l.prod.adjoint = (l.reverse.map ContinuousLinearMap.adjoint).prod := by
  induction l with
  | nil => simp [ContinuousLinearMap.adjoint_one]
  | cons a l ih =>
    simp only [List.prod_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    change (a.comp l.prod).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, ih]
    rfl

/-- The literal Hilbert adjoint reverses every factor, including each
letter's masks, scalar and physical conjugate (`measured-adjoint`,
`app:ch_regular:lem:finite-chain`). The original word uses the reversed list;
its adjoint uses this unreversed list of literal adjoints. -/
theorem orderedWord_adjoint {α X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] (T : α → X →L[ℂ] X)
    {j : ℕ} (w : Fin j → α) :
    (orderedWord T w).adjoint =
      (List.ofFn (fun k ↦ (T (w k)).adjoint)).prod := by
  simp only [orderedWord, adjoint_list_prod, List.reverse_reverse, List.map_ofFn]
  rfl

/-- Whole-operator reality intertwines every power with inclusion. No
individual residual letter is assumed real (`real-sector-normalization`,
`app:ch_regular:eq:chain-tail`). -/
theorem inclusion_realCompression_pow {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] {μ : Measure α}
    (P : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hP : conjugateOperator P.toLinearMap = P.toLinearMap) (j : ℕ)
    (u : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2ComplexInclusion μ ((realCompression P ^ j) u) =
      (P ^ j) (l2ComplexInclusion μ u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    rw [inclusion_realCompression P hP, ih]

/-- Compress the whole complex power, not its separate signed letters
(`real-sector-normalization`, `app:ch_regular:eq:chain-tail`). -/
theorem realCompression_pow {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] {μ : Measure α}
    (P : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hP : conjugateOperator P.toLinearMap = P.toLinearMap) (j : ℕ) :
    realCompression P ^ j = realCompression (P ^ j) := by
  ext1 u
  change _ = l2RealPart μ ((P ^ j) (l2ComplexInclusion μ u))
  rw [← inclusion_realCompression_pow P hP, realPart_inclusion]

/-- Compression distributes over the finite word sum without inserting a
real projection between any factors (`app:ch_regular:eq:chain-tail`). -/
theorem realCompression_sum {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {μ : Measure α}
    (T : κ → Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    realCompression (∑ a, T a) = ∑ a, realCompression (T a) := by
  ext1 u
  simp only [realCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', sum_apply, map_sum]

end JanetCartan.RegularSector.NormalizedResidualWords
