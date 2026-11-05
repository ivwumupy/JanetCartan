module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Expressions
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.WeakDerivatives

/-!
# Constructed ordered commutators of finite image factors

The recursion differentiates actual factors and consumes at most `s` datum
derivatives for a word of length `s+1`. Thus it constructs an `H^s → L²`
continuous linear map, with no commutator or Sobolev-action premise. The exact
weak identity is the input to `HigherRegularity.mem_succ_of_commutators` in
`app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential
namespace ImageFactorExpression

open PeriodicSobolevSpace ContinuumRow

variable {n : ℕ} {ι : Type*}
variable (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))

/-- Reverse-word commutator recursion. Each branch differentiates a coefficient
at least once; only the remaining derivatives can fall on the datum
(`app:ch_background:eq:bg-commutator`). -/
def reverseCommutator (e : ImageFactorExpression n ι) :
    (s : ℕ) → (is : List (Fin n)) → is.length ≤ s + 1 →
      (PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n)
  | _, [], _ => 0
  | 0, i :: _, _ => toL2 0 ∘L (e.coefficientDerivative i).onSobolev q hq 0
  | s + 1, i :: is, h =>
      reverseCommutator e s is (by simpa using h) ∘L coordinateDerivative s i +
        Exterior.reverseDerivativeToL2 (s + 1) is (by simpa using h) ∘L
          (e.coefficientDerivative i).onSobolev q hq (s + 1)

private theorem toL2_ofSmooth_eq (s t : ℕ) (f : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) : toL2 s (ofSmooth s f hf) = toL2 t (ofSmooth t f hf) := by
  apply MeasureTheory.Lp.ext
  exact (toL2_ofSmooth_ae s f hf).trans (toL2_ofSmooth_ae t f hf).symm

private theorem reverseDerivative_ofSmooth (s : ℕ) (is : List (Fin n))
    (h : is.length ≤ s) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    Exterior.reverseDerivativeToL2 s is h (ofSmooth s f hf) =
      toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse f)
        (hf.coordinateDerivList is.reverse)) := by
  simpa only [Exterior.derivativeToL2, List.reverse_reverse] using
    Exterior.derivativeToL2_ofSmooth s is.reverse (by simpa using h) f hf

/-- The recursive commutator equals the difference of the literal derivatives
on smooth data. The finite actions need no smooth-representative assumption
(`app:ch_background:eq:bg-commutator`). -/
theorem reverseDerivative_onSobolev_ofSmooth (e : ImageFactorExpression n ι)
    (s : ℕ) (is : List (Fin n)) (hlen : is.length ≤ s + 1)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    Exterior.reverseDerivativeToL2 (s + 1) is hlen
        (e.onSobolev q hq (s + 1) (ofSmooth (s + 1) f hf)) =
      e.onL2 q hq (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse f)
        (hf.coordinateDerivList is.reverse))) +
          e.reverseCommutator q hq s is hlen (ofSmooth s f hf) := by
  induction s generalizing is f with
  | zero =>
    cases is with
    | nil =>
      simp only [Exterior.reverseDerivativeToL2, List.reverse_nil,
        periodicCoordinateDerivList, reverseCommutator, zero_apply, add_zero,
        toL2_onSobolev, toL2_ofSmooth_eq 1 0]
    | cons i is =>
      have his : is = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst is
      simp only [Exterior.reverseDerivativeToL2, ContinuousLinearMap.comp_apply,
        coordinateDerivative_onSobolev, map_add, multiplier_inclusion_ofSmooth,
        coordinateDerivative_ofSmooth, toL2_onSobolev, reverseCommutator,
        List.reverse_cons, List.reverse_nil, List.nil_append,
        periodicCoordinateDerivList]
      exact add_comm _ _
  | succ s ih =>
    cases is with
    | nil =>
      simp only [Exterior.reverseDerivativeToL2, List.reverse_nil,
        periodicCoordinateDerivList, reverseCommutator, zero_apply, add_zero,
        toL2_onSobolev, toL2_ofSmooth_eq (s + 1 + 1) 0]
    | cons i is =>
      simp only [Exterior.reverseDerivativeToL2, ContinuousLinearMap.comp_apply,
        coordinateDerivative_onSobolev, map_add, multiplier_inclusion_ofSmooth,
        coordinateDerivative_ofSmooth, ih, reverseCommutator, add_apply,
        List.reverse_cons, periodicCoordinateDerivList_append, periodicCoordinateDerivList]
      abel

/-- The actual ordered commutator of length at most `s+1` is bounded from
`H^s` to L² by construction (`app:ch_background:eq:bg-commutator`). -/
def commutator (e : ImageFactorExpression n ι) (s : ℕ) (is : List (Fin n))
    (hlen : is.length ≤ s + 1) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n :=
  e.reverseCommutator q hq s is.reverse (by simpa using hlen)

/-- The exact smooth weak identity consumed by the higher elliptic bootstrap.
Every operator in this identity is constructed from the finite factors
(`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`). -/
theorem hasWeakDerivativeList_commutator (e : ImageFactorExpression n ι) (s : ℕ)
    (is : List (Fin n)) (hlen : is.length ≤ s + 1)
    (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    HasPeriodicWeakDerivativeList is
      (e.onL2 q hq (toL2 s (ofSmooth s f hf)))
      (e.onL2 q hq (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) + e.commutator q hq s is hlen (ofSmooth s f hf)) := by
  have h := HigherRegularity.hasWeakDerivativeList_derivativeToL2 (s + 1) is hlen
    (e.onSobolev q hq (s + 1) (ofSmooth (s + 1) f hf))
  rw [toL2_onSobolev, toL2_ofSmooth_eq (s + 1) s] at h
  have he := e.reverseDerivative_onSobolev_ofSmooth q hq s is.reverse
    (by simpa using hlen) f hf
  simpa only [Exterior.derivativeToL2, he, List.reverse_reverse, commutator] using h

end ImageFactorExpression
end JanetCartan.ContinuumCommutator.ImageChannel.Differential
