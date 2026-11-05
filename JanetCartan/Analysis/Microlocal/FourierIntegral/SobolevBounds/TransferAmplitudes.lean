module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PhaseTrade

/-!
# Full amplitudes and finite branches for nonlinear derivative transfer

The candidate coefficients in `app:ch_regular_base:eq:graph-derivative-transfer`.
The forward remainder differentiates both physical positions. In the reverse
remainder the derivative acts on the entire product of the mixed inverse and
the amplitude, retaining derivatives of inverse coefficients and all masks.

The reverse amplitudes are stored in the original `(x,y,η)` order. Start their
recursion with `C x y η = (A x y η).conjTranspose`; do not conjugate at every step.

The finite list is shared by the weak-transfer and primitive-budget proofs.
The theorems here only count its branches and datum orders; identifying its sum
with the actual operator derivative and bounding its amplitudes remain separate
analytic obligations. No such identity or bound is a field of this interface.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Forward transfer branch with no new datum derivative.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def graphTransferRemainder (S : Euclidean n → Euclidean n → ℝ)
    (i : Fin n) (A : FullAmplitude n r) : FullAmplitude n r :=
  fun x y η ↦ partialDeriv (fun z ↦ A z y η) x i +
    ∑ j, (mixedPhaseMatrix S x η i j : ℂ) • partialDeriv (fun z ↦ A x z η) y j

/-- Forward transfer branch carrying the `j`th datum derivative.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def graphTransferDatum (S : Euclidean n → Euclidean n → ℝ)
    (i j : Fin n) (A : FullAmplitude n r) : FullAmplitude n r :=
  fun x y η ↦ (mixedPhaseMatrix S x η i j : ℂ) • A x y η

/-- Reverse transfer branch carrying the `j`th datum derivative, with the
actual mixed inverse. `C` is already the reverse amplitude.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
def adjointTransferDatum (S : Euclidean n → Euclidean n → ℝ)
    (i j : Fin n) (C : FullAmplitude n r) : FullAmplitude n r :=
  fun x y η ↦ ((mixedPhaseMatrix S x η)⁻¹ i j : ℂ) • C x y η

/-- Reverse transfer remainder, including the derivative of the actual
inverse coefficient. `C` is already the reverse amplitude.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def adjointTransferRemainder (S : Euclidean n → Euclidean n → ℝ)
    (i : Fin n) (C : FullAmplitude n r) : FullAmplitude n r :=
  fun x y η ↦ partialDeriv (fun z ↦ C x z η) y i +
    ∑ j, partialDeriv (fun z ↦ adjointTransferDatum S i j C z y η) x j

/-- One remainder branch and one branch for each datum coordinate.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. Use the forward
coefficient pair or the reverse coefficient pair defined in this module. -/
def fullAmplitudeDerivativeStep
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (i : Fin n) (p : FullAmplitude n r × List (Fin n)) :
    List (FullAmplitude n r × List (Fin n)) :=
  (R i p.1, p.2) :: List.ofFn (fun j ↦ (P i j p.1, j :: p.2))

/-- Ordered finite branch list for the full-amplitude recurrence. The head
derivative acts last, consistently with the existing `orderedTransferAction`
convention. This defines coefficients; it does not assert an operator identity.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def fullAmplitudeDerivativeTerms
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (A : FullAmplitude n r) : List (Fin n) → List (FullAmplitude n r × List (Fin n))
  | [] => [(A, [])]
  | i :: is => (fullAmplitudeDerivativeTerms R P A is).flatMap
      (fullAmplitudeDerivativeStep R P i)

/-- Each nonlinear transfer has `n + 1` branches, counted with multiplicity.
Source: the finite sum in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeStep_length
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (i : Fin n) (p : FullAmplitude n r × List (Fin n)) :
    (fullAmplitudeDerivativeStep R P i p).length = n + 1 := by
  simp [fullAmplitudeDerivativeStep]

/-- The nonlinear expansion has `(n + 1)^s` branches before collecting terms.
Source: the finite sum in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_length
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (A : FullAmplitude n r) (is : List (Fin n)) :
    (fullAmplitudeDerivativeTerms R P A is).length = (n + 1) ^ is.length := by
  induction is with
  | nil => simp [fullAmplitudeDerivativeTerms]
  | cons i is ih =>
    simp [fullAmplitudeDerivativeTerms, List.length_flatMap,
      fullAmplitudeDerivativeStep_length, ih, pow_succ]

/-- Every datum word in the expansion has order at most the output word.
Source: the summation range in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_datum_length_le
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (A : FullAmplitude n r) (is : List (Fin n))
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) : p.2.length ≤ is.length := by
  induction is generalizing p with
  | nil =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_singleton] at hp
    subst p
    simp
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hlen := ih q hq
    simp only [fullAmplitudeDerivativeStep, List.mem_cons, List.mem_ofFn] at hp
    rcases hp with rfl | ⟨j, rfl⟩ <;> simp only [List.length_cons] <;> omega

end JanetCartan.FourierIntegral
