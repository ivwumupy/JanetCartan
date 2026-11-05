module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Ordered factor chains with matching carriers

Algebra for the last chain paragraphs of
`app:ch_response:thm:response-literal-transfer`. Each stage has its own space;
no identification of measures or insertion of envelope projections is made.
The consuming estimates are in `Response.Transfer.Chains`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open Finset

variable {ι : Type*} {E : ℕ → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]

/-- The first `n` factors, in their original order, in
`app:ch_response:eq:fixed-factor-transfer`. The index includes frequency and data. -/
def factorChain (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1)) (f : ι → E 0) :
    (n : ℕ) → ι → E n
  | 0 => f
  | n + 1 => fun i ↦ T n i (factorChain T f n i)

/-- The term with the complementary factor at position `j`: near factors before
it and full factors after it (`app:ch_response:thm:response-literal-transfer`).
Terms beyond the length are zero. -/
def chainLeakage (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1)) (f : ι → E 0) :
    (n : ℕ) → ℕ → ι → E n
  | 0, _ => fun _ ↦ 0
  | n + 1, j => fun i ↦ if j = n then C n i (factorChain N f n i)
      else T n i (chainLeakage T N C f n j i)

/-- Exact noncommutative telescoping, with every original full downstream factor
retained (`app:ch_response:thm:response-literal-transfer`). -/
theorem factorChain_eq_near_add_leakage
    (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1)) (f : ι → E 0) (d : ℕ)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i) :
    ∀ n ≤ d, ∀ i, factorChain T f n i = factorChain N f n i +
      ∑ j ∈ range n, chainLeakage T N C f n j i := by
  intro n hn
  induction n with
  | zero => simp [factorChain]
  | succ n ih =>
    intro i
    have hi := ih (Nat.le_trans (Nat.le_succ n) hn) i
    have hnd : n < d := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    simp only [factorChain]
    rw [hi, map_add, map_sum, sum_range_succ]
    have hterms : (∑ j ∈ range n, chainLeakage T N C f (n + 1) j i) =
        ∑ j ∈ range n, T n i (chainLeakage T N C f n j i) := by
      apply sum_congr rfl
      intro j hj
      simp [chainLeakage, Nat.ne_of_lt (mem_range.mp hj)]
    rw [hterms]
    simp only [chainLeakage, ↓reduceIte]
    rw [hsplit n hnd i, LinearMap.add_apply]
    ac_rfl

/-- Exact cancellation of adjacent carrier multiplications. A single equivalence
at each stage expresses explicitly matching input/output carriers; in applications
these are the physical exponentials of `app:ch_response:eq:fixed-factor-transfer`.
No boundedness or measure identification is inferred from this identity. -/
theorem factorChain_matching_carriers
    (T B : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j ≃ₗ[ℝ] E j) (f : ι → E 0) (d : ℕ)
    (hmatch : ∀ j < d, ∀ i v, B j i v =
      (M (j + 1) i).symm (T j i (M j i v))) :
    ∀ n ≤ d, ∀ i, factorChain B f n i =
      (M n i).symm (factorChain T (fun k ↦ M 0 k (f k)) n i) := by
  intro n hn
  induction n with
  | zero => simp [factorChain]
  | succ n ih =>
    intro i
    simp only [factorChain]
    rw [hmatch n (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn),
      ih (Nat.le_trans (Nat.le_succ n) hn), LinearEquiv.apply_symm_apply]

end JanetCartan.ResponseTransfer
