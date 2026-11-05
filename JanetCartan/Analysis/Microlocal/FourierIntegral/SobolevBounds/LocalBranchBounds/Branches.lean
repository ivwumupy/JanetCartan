module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.LocalBranchBounds.Expansion

/-!
# Uniform primitive counts for both graph transfer recursions

For the low seminorm estimate preceding `app:ch_regular_base:eq:fio-input`,
these counts are independent of the phase, amplitude, and high seminorms.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A F : FullAmplitude n r}

variable {U : Set (Point n)}

/-- The forward remainder has at most `n+1` coordinate contributions, each
with at most `m+1` Leibniz terms per original monomial.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem BoundedExpansionOn.graph_remainder (hU : IsOpen U) (h : SmoothPrimitivesOn S A U) {b N m : ℕ}
    (hF : BoundedExpansionOn S A F U b N m) (i : Fin n) :
    BoundedExpansionOn S A (graphTransferRemainder S i F) U
      (b + 1) ((n + 1) * (N * (m + 1))) (m + 1) := by
  have he : graphTransferRemainder S i F = FullAmplitudePrimitiveBudget.derivative (.left, i) F +
      ∑ j, FullAmplitudePrimitiveBudget.multiply (scalarPrimitive S (false, i, j)) (FullAmplitudePrimitiveBudget.derivative (.right, j) F) := by
    funext x y η
    simp [graphTransferRemainder, FullAmplitudePrimitiveBudget.derivative, slice, anchor, FullAmplitudePrimitiveBudget.multiply, scalarPrimitive]
  rw [he]
  have hd (c : Coordinate n) := (hF.derivative hU h c).mono le_rfl
    (Nat.mul_le_mul_left N (Nat.le_succ m)) le_rfl
  have hsum := BoundedExpansionOn.sum Finset.univ _ (b + 1) (N * (m + 1)) (m + 1)
    (fun j _ => (hd (.right, j)).multiply (false, i, j))
  simpa [Nat.add_mul, Nat.add_comm] using
    ((hd (.left, i)).mono le_rfl le_rfl (Nat.le_succ m)).add hsum

/-- The reverse remainder differentiates the complete inverse-weighted
amplitude, and obeys the same count including derivatives of the inverse.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem BoundedExpansionOn.adjoint_remainder (hU : IsOpen U) (h : SmoothPrimitivesOn S A U) {b N m : ℕ}
    (hF : BoundedExpansionOn S A F U b N m) (i : Fin n) :
    BoundedExpansionOn S A (adjointTransferRemainder S i F) U
      (b + 1) ((n + 1) * (N * (m + 1))) (m + 1) := by
  have he : adjointTransferRemainder S i F = FullAmplitudePrimitiveBudget.derivative (.right, i) F +
      ∑ j, FullAmplitudePrimitiveBudget.derivative (.left, j) (FullAmplitudePrimitiveBudget.multiply (scalarPrimitive S (true, i, j)) F) := by
    funext x y η
    simp [adjointTransferRemainder, adjointTransferDatum,
      FullAmplitudePrimitiveBudget.derivative, slice, anchor, FullAmplitudePrimitiveBudget.multiply, scalarPrimitive]
  rw [he]
  have hd := (hF.derivative hU h (.right, i)).mono le_rfl
    (Nat.mul_le_mul_left N (Nat.le_succ m)) (Nat.le_succ m)
  have hsum := BoundedExpansionOn.sum Finset.univ _ (b + 1) (N * (m + 1)) (m + 1)
    (fun j _ => (hF.multiply (true, i, j)).derivative hU h (.left, j))
  simpa [Nat.add_mul, Nat.add_comm] using hd.add hsum

private theorem bounded_branch_expansion
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (hR : ∀ F b N m, BoundedExpansionOn S A F U b N m → ∀ i,
      BoundedExpansionOn S A (R i F) U (b + 1) ((n + 1) * (N * (m + 1))) (m + 1))
    (hP : ∀ F b N m, BoundedExpansionOn S A F U b N m → ∀ i j,
      BoundedExpansionOn S A (P i j F) U b N (m + 1))
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) :
    BoundedExpansionOn S A p.1 U (is.length - p.2.length)
      (branchTermCount n is.length) (is.length + 1) := by
  induction is generalizing p with
  | nil =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_singleton] at hp
    subst p
    exact BoundedExpansionOn.amplitude
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hb := ih q hq
    have hlen := fullAmplitudeDerivativeTerms_datum_length_le R P A is q hq
    simp only [fullAmplitudeDerivativeStep, List.mem_cons, List.mem_ofFn] at hp
    rcases hp with rfl | ⟨j, rfl⟩
    · convert hR q.1 _ _ _ hb i using 1 <;>
        simp only [List.length_cons, branchTermCount, Nat.add_assoc]
      omega
    · have hd := (hP q.1 _ _ _ hb i j).mono le_rfl
        (branchTermCount_le_succ n is.length) le_rfl
      simpa using hd

/-- Concrete forward branches have at most `s+1` primitive factors, and a
number of summands depending only on dimension and output order.
Source: the uniform constant in `app:ch_regular_base:eq:fio-input`. -/
theorem graph_branch_bounded_expansion (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is) :
    BoundedExpansionOn S A p.1 U (is.length - p.2.length)
      (branchTermCount n is.length) (is.length + 1) :=
  bounded_branch_expansion _ _ (fun _ _ _ _ hF => hF.graph_remainder hU h)
    (fun _ _ _ _ hF i j => hF.multiply (false, i, j)) is p hp

/-- The same uniform counts for the literal reverse branches, initialized
with the already conjugate-transposed complete amplitude.
Source: the uniform constant in `app:ch_regular_base:eq:fio-input`. -/
theorem adjoint_branch_bounded_expansion (hU : IsOpen U) (h : SmoothPrimitivesOn S A U)
    (is : List (Fin n)) (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is) :
    BoundedExpansionOn S A p.1 U (is.length - p.2.length)
      (branchTermCount n is.length) (is.length + 1) :=
  bounded_branch_expansion _ _ (fun _ _ _ _ hF => hF.adjoint_remainder hU h)
    (fun _ _ _ _ hF i j => hF.multiply (true, i, j)) is p hp

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
