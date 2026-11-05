module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Frobenius jets and ordered matrix coordinate derivatives

Conversion used by the transport and inverse amplitudes in
`app:ch_osc:prop:osc-normal` to apply `app:ch_osc:lem:osc-amplitude`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {d r : ℕ}

local instance transportCoordinateMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Matrix-valued ordered directional derivatives for the coefficient conversion
in `app:ch_osc:prop:osc-normal`. -/
def normalMatrixDerivList : List (Fin d) →
    (EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ) →
    EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ
  | [], f => f
  | i :: is, f => fun z ↦ fderiv ℝ (normalMatrixDerivList is f) z
      (EuclideanSpace.single i 1)

/-- Smoothness of the ordered matrix derivatives in
`app:ch_osc:prop:osc-normal`. -/
theorem contDiff_normalMatrixDerivList
    {f : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin d)) :
    ContDiff ℝ ∞ (normalMatrixDerivList is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- The matrix derivative agrees with the entrywise API of the two-position
amplitude lemma (`app:ch_osc:lem:osc-amplitude`). -/
theorem normalMatrixDerivList_eq_matrixAmplitudeCoordinateDerivList
    {f : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin d)) :
    normalMatrixDerivList is f = matrixAmplitudeCoordinateDerivList is f := by
  induction is with
  | nil => rfl
  | cons a is ih =>
    funext z i j
    have hd := (contDiff_normalMatrixDerivList hf is).differentiable (by simp) z
    have he := ((matrixEntryEvaluation i j).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
    have hh : (fun w ↦ normalMatrixDerivList is f w i j) =
        euclideanCoordinateDerivList is (fun w ↦ f w i j) := by
      funext w
      exact congrFun (congrFun (congrFun ih w) i) j
    change (fderiv ℝ (normalMatrixDerivList is f) z (EuclideanSpace.single a 1)) i j =
      fderiv ℝ (euclideanCoordinateDerivList is (fun w ↦ f w i j)) z
        (EuclideanSpace.single a 1)
    rw [← hh]
    exact (congrArg (fun L ↦ L (EuclideanSpace.single a 1)) he).symm

/-- Each ordered coordinate derivative costs exactly its order in full
Frobenius jets, for `app:ch_osc:prop:osc-normal`. -/
theorem norm_iteratedFDeriv_normalMatrixDerivList_le
    {f : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin d)) (k : ℕ) (z) :
    ‖iteratedFDeriv ℝ k (normalMatrixDerivList is f) z‖ ≤
      ‖iteratedFDeriv ℝ (k + is.length) f z‖ := by
  induction is generalizing k with
  | nil => simp [normalMatrixDerivList]
  | cons i is ih =>
    let L := ContinuousLinearMap.apply ℝ (Matrix (Fin r) (Fin r) ℂ)
      (EuclideanSpace.single i (1 : ℝ))
    have hL : ‖L‖ ≤ 1 := by
      apply L.opNorm_le_bound zero_le_one
      intro A
      exact (A.le_opNorm _).trans (by simp [EuclideanSpace.single, PiLp.norm_single])
    have h := L.norm_iteratedFDeriv_comp_left
      (((contDiff_normalMatrixDerivList hf is).fderiv_right (m := ∞) (by simp)).contDiffAt (x := z))
      (n := k) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    have hb := h.trans (by simpa using (mul_le_mul_of_nonneg_right hL
      (norm_nonneg (iteratedFDeriv ℝ (k + 1) (normalMatrixDerivList is f) z))))
    apply hb.trans
    have hi := ih (k + 1)
    have he : k + 1 + is.length = k + (i :: is).length := by simp; omega
    rw [he] at hi
    exact hi

/-- Reusable conversion from global Frobenius jets to the exact entrywise matrix
coordinate derivatives of `app:ch_osc:lem:osc-amplitude`. -/
theorem norm_matrixAmplitudeCoordinateDerivList_le_jet
    {f : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin d)) (z) :
    ‖matrixAmplitudeCoordinateDerivList is f z‖ ≤
      ‖iteratedFDeriv ℝ is.length f z‖ := by
  rw [← normalMatrixDerivList_eq_matrixAmplitudeCoordinateDerivList hf]
  have h := norm_iteratedFDeriv_normalMatrixDerivList_le hf is 0 z
  rw [Nat.zero_add, norm_iteratedFDeriv_zero] at h
  exact h

end JanetCartan.NormalComparison
