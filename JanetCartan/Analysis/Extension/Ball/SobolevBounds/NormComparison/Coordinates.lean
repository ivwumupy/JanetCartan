module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Definitions

/-!
# Iterated Cartesian differentiation on open sets

The multiindex derivatives in `app:ch_regular_base:lem:ball-extension` are
actual repeated coordinate derivatives. This module identifies their canonical
Fréchet-jet definition with successive coordinate differentiation on open sets.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.BallExtension

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Successive Cartesian coordinate derivatives, with the head of the list
acting last, for `app:ch_regular_base:lem:ball-extension`. This real-domain,
arbitrary-codomain version also applies to intermediate Fréchet jets. -/
def cartesianCoordinateDerivList :
    List (Fin n) → (EuclideanSpace ℝ (Fin n) → F) → EuclideanSpace ℝ (Fin n) → F
  | [], f => f
  | i :: is, f => fun x ↦ fderiv ℝ (cartesianCoordinateDerivList is f) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Repeated coordinate derivatives remain smooth on the open domain in
`app:ch_regular_base:lem:ball-extension`. This also applies to vector-valued
intermediate derivatives, without an ambient smoothness hypothesis. -/
theorem contDiffOn_cartesianCoordinateDerivList
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f s)
    (is : List (Fin n)) : ContDiffOn ℝ ∞ (cartesianCoordinateDerivList is f) s := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    have h := (ih.fderivWithin hs.uniqueDiffOn (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin n) ℝ i))
    apply h.congr
    intro x hx
    simp only [cartesianCoordinateDerivList, fderivWithin_of_isOpen hs hx]

/-- On an open set, repeated coordinate differentiation equals evaluation of
the iterated Fréchet derivative on the corresponding basis vectors
(`app:ch_regular_base:lem:ball-extension`). No global smoothness is required. -/
theorem cartesianCoordinateDerivList_eq_iteratedFDerivWithin
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f s)
    (is : List (Fin n)) :
    EqOn (cartesianCoordinateDerivList is f)
      (fun x ↦ iteratedFDerivWithin ℝ is.length f s x
        (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ (is.get j))) s := by
  induction is with
  | nil =>
    intro x _
    simp [cartesianCoordinateDerivList, iteratedFDerivWithin_zero_apply]
  | cons i is ih =>
    intro x hx
    change fderiv ℝ (cartesianCoordinateDerivList is f) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) = _
    rw [← fderivWithin_of_isOpen hs hx, fderivWithin_congr' ih hx,
      fderivWithin_continuousMultilinear_apply_const_apply (hs.uniqueDiffOn x hx)
        (hf.differentiableOn_iteratedFDerivWithin (m := is.length)
          (by exact_mod_cast ENat.natCast_lt_top is.length) hs.uniqueDiffOn x hx)]
    rfl

/-- The canonical multiindex jet is precisely the repeated Cartesian derivative
used in the norm preceding `app:ch_regular_base:lem:ball-extension`. -/
theorem cartesianDerivativeWithin_eq_coordinateDerivList
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f s)
    (α : Fin n → ℕ) :
    EqOn (cartesianDerivativeWithin α f s)
      (cartesianCoordinateDerivList (sobolevDerivativeList α) f) s :=
  (cartesianCoordinateDerivList_eq_iteratedFDerivWithin hs hf _).symm

end JanetCartan.BallExtension
