module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Smooth
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Literal multiplication and ordered Sobolev derivatives

Operators used to realize the fixed exterior part of
`app:ch_background:eq:bg-commutator` on every Sobolev datum.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.Exterior

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]


/-- Literal real scalar multiplication on L², for the exterior normal in
`app:ch_background:prop:bg-inverse`. -/
def multiplication (q : Torus n → ℝ) (hq : Continuous q) :
    PeriodicL2 n F →L[ℝ] PeriodicL2 n F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).holderL volume ∞ 2 2
    ((hq.memLp_of_hasCompactSupport (p := ∞) (HasCompactSupport.of_compactSpace q)).toLp q)

/-- The multiplier has the actual pointwise representative
(`app:ch_background:eq:bg-commutator`). -/
theorem multiplication_ae (q : Torus n → ℝ) (hq : Continuous q) (u : PeriodicL2 n F) :
    multiplication q hq u =ᵐ[volume] fun x ↦ q x • u x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := F)).coeFn_holder (r := 2)
    ((hq.memLp_of_hasCompactSupport (p := ∞) (HasCompactSupport.of_compactSpace q)).toLp q) u,
    (hq.memLp_of_hasCompactSupport (p := ∞) (HasCompactSupport.of_compactSpace q)).coeFn_toLp]
    with x hx hq'
  exact hx.trans (congrArg (fun a : ℝ ↦ a • u x) hq')

variable [FiniteDimensional ℝ F]

open PeriodicSobolevSpace

/-- Multiplication agrees with the classical smooth product at every chosen
Sobolev realization (`app:ch_background:eq:bg-commutator`). -/
theorem multiplication_ofSmooth {q : Torus n → ℝ} {f : Torus n → F}
    (hq : IsSmoothPeriodic q) (hf : IsSmoothPeriodic f) (s t : ℕ) :
    multiplication q hq.1 (toL2 s (ofSmooth s f hf)) =
      toL2 t (ofSmooth t (fun x ↦ q x • f x) (smooth_smul hq hf)) := by
  apply Lp.ext
  filter_upwards [multiplication_ae q hq.1 (toL2 s (ofSmooth s f hf)),
    toL2_ofSmooth_ae s f hf, toL2_ofSmooth_ae t _ (smooth_smul hq hf)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

/-- Recursive lower derivative, consuming coordinates from left to right.
Reversing the word below gives the ordered operator in
`app:ch_background:eq:bg-commutator`. -/
def reverseDerivativeToL2 : (s : ℕ) → (is : List (Fin n)) → is.length ≤ s →
    PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F
  | s, [], _ => toL2 s
  | 0, _ :: _, h => False.elim (by simp at h)
  | s + 1, i :: is, h =>
      (reverseDerivativeToL2 s is (by simpa using h)).comp (coordinateDerivative s i)

private theorem reverseDerivativeToL2_ofSmooth (s : ℕ) (is : List (Fin n)) (h : is.length ≤ s)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    reverseDerivativeToL2 s is h (ofSmooth s f hf) =
      toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse f)
        (hf.coordinateDerivList is.reverse)) := by
  induction s generalizing is f with
  | zero =>
    have he : is = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst is
    rfl
  | succ s ih =>
    cases is with
    | nil =>
      apply Lp.ext
      exact (toL2_ofSmooth_ae (s + 1) f hf).trans (toL2_ofSmooth_ae 0 f hf).symm
    | cons i is =>
      simp only [reverseDerivativeToL2, ContinuousLinearMap.comp_apply,
        coordinateDerivative_ofSmooth, ih, List.reverse_cons,
        periodicCoordinateDerivList_append, periodicCoordinateDerivList]

/-- The lower derivative of an `H^s` datum, obtained by composing the shared
bounded coordinate weak derivatives and then including in L². The reversed
iteration implements the exact ordered classical word
(`app:ch_background:eq:bg-commutator`). -/
def derivativeToL2 (s : ℕ) (is : List (Fin n)) (h : is.length ≤ s) :
    PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F :=
  reverseDerivativeToL2 s is.reverse (by simpa using h)

/-- Literal smooth representative of each lower derivative
(`app:ch_background:eq:bg-commutator`). -/
theorem derivativeToL2_ofSmooth (s : ℕ) (is : List (Fin n)) (h : is.length ≤ s)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    derivativeToL2 s is h (ofSmooth s f hf) =
      toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is)) := by
  simp only [derivativeToL2, reverseDerivativeToL2_ofSmooth, List.reverse_reverse]

end JanetCartan.ContinuumCommutator.Exterior
