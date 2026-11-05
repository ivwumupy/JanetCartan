module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives

/-!
# Coordinate words for physical adjoint derivatives

For `app:ch_background:prop:bg-adjoint`, connect the actual derivative words of
`Iteration` to the ordered coordinates of `CarrierSobolev.WeakDerivatives`.
The consumer is the construction of physical weak derivatives after the partial
radian inverse Fourier transform. These definitions introduce no new norm or
analytic hypothesis. In particular, initial letters multiply by `i⟪h,η⟫`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential

variable {n s : ℕ}

/-- The scalar and both vector carrier directions, in the order used by
`flatInitialCoordinates` in `app:ch_background:prop:bg-adjoint`. -/
def physicalCarrierDirection (i : Fin 3) : CarrierParameter :=
  Fin.cases (1, 0) (fun j ↦ (0, EuclideanSpace.basisFun (Fin 2) ℝ j)) i

/-- The initial basis directions agree with the published ordered coordinate
map, for the distributional transfer in `app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialCoordinates_initialDirection (i : Fin (n - 1)) :
    flatInitialCoordinates n (0, EuclideanSpace.basisFun (Fin (n - 1)) ℝ i) =
      EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ (Fin.natAdd 3 i) := by
  ext j
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl]
      change flatInitialEquiv n (initialCoordinates n _) _ = _
      rw [flatInitialEquiv_scalar]
      simp [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
    · rw [show k.succ = Fin.natAdd 1 k by
        ext; simp only [Fin.val_succ, Fin.val_natAdd]; omega]
      change flatInitialEquiv n (initialCoordinates n _)
        (Fin.castAdd (n - 1) (Fin.natAdd 1 k)) = _
      rw [flatInitialEquiv_vector]
      simp [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
      omega
  · change flatInitialEquiv n (initialCoordinates n _) (Fin.natAdd 3 k) = _
    rw [flatInitialEquiv_transverse]
    simp

/-- All three carrier basis directions agree with the published ordered
coordinate map, for `app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialCoordinates_physicalCarrierDirection (i : Fin 3) :
    flatInitialCoordinates n (physicalCarrierDirection i, 0) =
      EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ (Fin.castAdd (n - 1) i) := by
  ext j
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl]
      change flatInitialEquiv n (initialCoordinates n _) _ = _
      rw [flatInitialEquiv_scalar]
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · simp [physicalCarrierDirection]
      · simp [physicalCarrierDirection]
    · rw [show k.succ = Fin.natAdd 1 k by
        ext; simp only [Fin.val_succ, Fin.val_natAdd]; omega]
      change flatInitialEquiv n (initialCoordinates n _)
        (Fin.castAdd (n - 1) (Fin.natAdd 1 k)) = _
      rw [flatInitialEquiv_vector]
      have hk : Fin.natAdd 1 k = k.succ := by
        ext
        simp only [Fin.val_succ, Fin.val_natAdd]
        omega
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · simp [physicalCarrierDirection, hk]
      · simp [physicalCarrierDirection, hk]
  · change flatInitialEquiv n (initialCoordinates n _) (Fin.natAdd 3 k) = _
    rw [flatInitialEquiv_transverse]
    simp [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
    omega

/-- All physical coordinate letters, including all three carrier coordinates
and every initial coordinate, for `app:ch_background:prop:bg-adjoint`. -/
def physicalCoordinateDerivativeLetter (i : Fin (3 + (n - 1))) :
    InitialCarrierDerivative n :=
  Fin.addCases (fun j ↦ .carrier (physicalCarrierDirection j))
    (fun j ↦ .initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ j)) i

/-- Carrier coordinates select actual carrier derivatives in the adjoint
expansion (`app:ch_background:eq:bg-derivative-trade`). -/
@[simp] theorem physicalCoordinateDerivativeLetter_castAdd (i : Fin 3) :
    physicalCoordinateDerivativeLetter (Fin.castAdd (n - 1) i) =
      .carrier (physicalCarrierDirection i) := by
  simp [physicalCoordinateDerivativeLetter]

/-- Initial coordinates select the radian multiplier, with no extra `2π`,
in `app:ch_background:eq:bg-derivative-trade`. -/
@[simp] theorem physicalCoordinateDerivativeLetter_natAdd (i : Fin (n - 1)) :
    physicalCoordinateDerivativeLetter (Fin.natAdd 3 i) =
      .initial (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i) := by
  simp [physicalCoordinateDerivativeLetter]

/-- Concatenation composes the actual derivative operators; the leftmost
letter acts last (`app:ch_background:prop:bg-adjoint`). -/
theorem applyInitialCarrierDerivativeList_append
    (ds es : List (InitialCarrierDerivative n)) (f : CarrierVariable n → ℂ) :
    applyInitialCarrierDerivativeList (ds ++ es) f =
      applyInitialCarrierDerivativeList ds (applyInitialCarrierDerivativeList es f) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append, applyInitialCarrierDerivativeList, ih]

/-- Joint smoothness is preserved by every actual derivative letter. This
supplies the regularity input for successive partial Fourier transfers in
`app:ch_background:prop:bg-adjoint`; it is not a Fourier intertwining premise. -/
theorem contDiff_applyInitialCarrierDerivative_joint
    {f : CarrierVariable n → ℂ} (hf : ContDiff ℝ ∞ f)
    (d : InitialCarrierDerivative n) : ContDiff ℝ ∞ (applyInitialCarrierDerivative d f) := by
  cases d with
  | initial h =>
    exact (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp ((innerSL ℝ h).contDiff.comp contDiff_snd))).mul hf
  | carrier h =>
    have hr : ContDiff ℝ ∞ (fun p : CarrierVariable n × CarrierParameter ↦
        f (p.2, p.1.2)) := hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
    exact hr.fderiv_apply contDiff_fst contDiff_const (by simp)

/-- Every actual word is jointly smooth when the original function is jointly
smooth, for the iterated transfer in `app:ch_background:prop:bg-adjoint`. -/
theorem contDiff_applyInitialCarrierDerivativeList_joint
    {f : CarrierVariable n → ℂ} (hf : ContDiff ℝ ∞ f)
    (ds : List (InitialCarrierDerivative n)) :
    ContDiff ℝ ∞ (applyInitialCarrierDerivativeList ds f) := by
  induction ds with
  | nil => exact hf
  | cons d ds ih => exact contDiff_applyInitialCarrierDerivative_joint ih d

/-- Translate a finite physical derivative index to the actual word in the
adjoint expansion (`app:ch_background:prop:bg-adjoint`). A branch indexed by
`(i,w)` differentiates first in `i`, so its letter is appended on the right. -/
def physicalDerivativeWord : {s : ℕ} → CarrierDerivativeIndex n s →
    List (InitialCarrierDerivative n)
  | 0, _ => []
  | _ + 1, none => []
  | _ + 1, some (i, w) => physicalDerivativeWord w ++ [physicalCoordinateDerivativeLetter i]

/-- The root represents the original adjoint, for
`app:ch_background:prop:bg-adjoint`. -/
@[simp] theorem physicalDerivativeWord_empty (s : ℕ) :
    physicalDerivativeWord (n := n) (.empty (3 + (n - 1)) s) = [] := by
  cases s <;> rfl

/-- The translated word uses at most its allotted number of derivatives in
`app:ch_background:prop:bg-adjoint`. -/
theorem physicalDerivativeWord_length_le (w : CarrierDerivativeIndex n s) :
    (physicalDerivativeWord w).length ≤ s := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    cases w with
    | none => exact Nat.zero_le _
    | some p =>
      simpa only [physicalDerivativeWord, List.length_append, List.length_singleton]
        using Nat.add_le_add_right (ih p.2) 1

/-- Increasing the derivative budget does not change an actual word in
`app:ch_background:prop:bg-adjoint`. -/
@[simp] theorem physicalDerivativeWord_raise (w : CarrierDerivativeIndex n s) :
    physicalDerivativeWord w.raise = physicalDerivativeWord w := by
  induction s with
  | zero => rfl
  | succ s ih =>
    cases w with
    | none => rfl
    | some p => simp only [EuclideanDerivativeIndex.raise, physicalDerivativeWord, ih]

/-- Branch recursion agrees exactly with the shared weak derivative family
recursion, without commuting derivative letters
(`app:ch_background:prop:bg-adjoint`). -/
theorem apply_physicalDerivativeWord_some
    (i : Fin (3 + (n - 1))) (w : CarrierDerivativeIndex n s)
    (f : CarrierVariable n → ℂ) :
    applyInitialCarrierDerivativeList (physicalDerivativeWord (n := n) (s := s + 1)
      (some (i, w))) f =
      applyInitialCarrierDerivativeList (physicalDerivativeWord w)
        (applyInitialCarrierDerivative (physicalCoordinateDerivativeLetter i) f) := by
  rw [physicalDerivativeWord, applyInitialCarrierDerivativeList_append]
  rfl

end JanetCartan.ContinuumAdjoint.DerivativeKernels
