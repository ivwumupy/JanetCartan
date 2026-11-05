module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveBudget.Expansion

/-!
# Primitive expansions of the concrete nonlinear graph branches

Step 3 of `app:ch_regular_base:thm:actual-calculus`, between
`app:ch_regular_base:eq:graph-derivative-transfer` and
`app:ch_regular_base:eq:fio-input`. Both recursions are the actual full-amplitude
recursions. The reverse input is already conjugate-transposed; differentiating
its remainder differentiates the actual inverse as well as the amplitude.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F : FullAmplitude n r}

/-- A forward datum branch adds an undifferentiated actual mixed entry.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem Expansion.graph_datum {b : ℕ} (hF : Expansion S A F b) (i j : Fin n) :
    Expansion S A (graphTransferDatum S i j F) b :=
  hF.multiply (false, i, j)

/-- A reverse datum branch adds an undifferentiated actual inverse entry.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem Expansion.adjoint_datum {b : ℕ} (hF : Expansion S A F b) (i j : Fin n) :
    Expansion S A (adjointTransferDatum S i j F) b :=
  hF.multiply (true, i, j)

/-- The forward remainder spends one shared derivative, in either position.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem Expansion.graph_remainder (h : SmoothPrimitives S A) {b : ℕ}
    (hF : Expansion S A F b) (i : Fin n) :
    Expansion S A (graphTransferRemainder S i F) (b + 1) := by
  have he : graphTransferRemainder S i F = FullAmplitudePrimitiveBudget.derivative (.left, i) F +
      ∑ j, FullAmplitudePrimitiveBudget.multiply (scalarPrimitive S (false, i, j))
        (FullAmplitudePrimitiveBudget.derivative (.right, j) F) := by
    funext x y η
    simp [graphTransferRemainder, FullAmplitudePrimitiveBudget.derivative, slice, anchor,
      FullAmplitudePrimitiveBudget.multiply, scalarPrimitive]
  rw [he]
  exact (hF.derivative h (.left, i)).add
    (Expansion.sum Finset.univ _ _ (fun j _ =>
      (hF.derivative h (.right, j)).multiply (false, i, j)))

/-- The reverse remainder differentiates the entire inverse-times-amplitude
product. Thus inverse derivatives are retained, at the same shared cost one.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem Expansion.adjoint_remainder (h : SmoothPrimitives S A) {b : ℕ}
    (hF : Expansion S A F b) (i : Fin n) :
    Expansion S A (adjointTransferRemainder S i F) (b + 1) := by
  have he : adjointTransferRemainder S i F = FullAmplitudePrimitiveBudget.derivative (.right, i) F +
      ∑ j, FullAmplitudePrimitiveBudget.derivative (.left, j)
        (FullAmplitudePrimitiveBudget.multiply (scalarPrimitive S (true, i, j)) F) := by
    funext x y η
    simp [adjointTransferRemainder, adjointTransferDatum,
      FullAmplitudePrimitiveBudget.derivative, slice, anchor,
      FullAmplitudePrimitiveBudget.multiply, scalarPrimitive]
  rw [he]
  exact (hF.derivative h (.right, i)).add
    (Expansion.sum Finset.univ _ _ (fun j _ =>
      (hF.multiply (true, i, j)).derivative h (.left, j)))

private theorem branch_expansion
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (hR : ∀ F b, Expansion S A F b → ∀ i, Expansion S A (R i F) (b + 1))
    (hP : ∀ F b, Expansion S A F b → ∀ i j, Expansion S A (P i j F) b)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) :
    Expansion S A p.1 (is.length - p.2.length) := by
  induction is generalizing p with
  | nil =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_singleton] at hp
    subst p
    exact Expansion.amplitude
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hb := ih q hq
    have hlen := fullAmplitudeDerivativeTerms_datum_length_le R P A is q hq
    simp only [fullAmplitudeDerivativeStep, List.mem_cons, List.mem_ofFn] at hp
    rcases hp with rfl | ⟨j, rfl⟩
    · convert hR q.1 _ hb i using 1
      simp only [List.length_cons]
      omega
    · simpa using hP q.1 _ hb i j

/-- Every concrete forward branch with output order `s` and datum order `k`
is a finite sum of primitive products of total derivative order at most `s-k`.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_branch_expansion (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is) : Expansion S A p.1 (is.length - p.2.length) :=
  branch_expansion _ _ (fun _ _ hF => hF.graph_remainder h)
    (fun _ _ hF => hF.graph_datum) is p hp

/-- Every concrete reverse branch has the same joint budget. `A` here is the
already conjugate-transposed complete amplitude; it is never reconjugated.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem adjoint_branch_expansion (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is) : Expansion S A p.1 (is.length - p.2.length) :=
  branch_expansion _ _ (fun _ _ hF => hF.adjoint_remainder h)
    (fun _ _ hF => hF.adjoint_datum) is p hp

/-- The additional joint seminorm word costs only its length, for a concrete
forward branch. Source: the `μ₀` count in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem graph_branch_jet_expansion (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is) (w : List (Coordinate n)) :
    Expansion S A (jet w p.1) (is.length - p.2.length + w.length) :=
  (graph_branch_expansion h is p hp).jet h w

/-- The same seminorm count for the literal reverse graph, including covector
and inverse derivatives. Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem adjoint_branch_jet_expansion (h : SmoothPrimitives S A)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is) (w : List (Coordinate n)) :
    Expansion S A (jet w p.1) (is.length - p.2.length + w.length) :=
  (adjoint_branch_expansion h is p hp).jet h w

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
