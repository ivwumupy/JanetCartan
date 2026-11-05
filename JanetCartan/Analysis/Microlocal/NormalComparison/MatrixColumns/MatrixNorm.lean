module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns.Kernels
public import Mathlib.Analysis.Matrix.Normed

/-!
# Original matrix amplitude bounds on its columns

The fixed matrix norm in `app:ch_osc:prop:osc-normal` can be taken to be the
Frobenius norm.  Each actual Euclidean column is bounded by that norm, and
the column projection is continuous.  These facts discharge the column
inputs of the actual fixed-parameter construction.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The actual column amplitude is bounded by the original Frobenius
matrix amplitude (`app:ch_osc:prop:osc-normal`). -/
theorem norm_matrixAmplitudeColumn_le (a : Matrix I J ℂ) (j : J) :
    ‖matrixAmplitudeColumn a j‖ ≤ ‖a‖ := by
  have h := PiLp.norm_apply_le
    (WithLp.toLp 2 (fun j : J ↦ WithLp.toLp 2 (fun i : I ↦ a i j))) j
  change ‖matrixAmplitudeColumn a j‖ ≤ ‖a.transpose‖ at h
  simpa only [Matrix.frobenius_norm_transpose] using h

/-- Projection of the original rectangular matrix to its actual column,
with no dimension-dependent change of the amplitude size
(`app:ch_osc:prop:osc-normal`). -/
def matrixAmplitudeColumnCLM (j : J) : Matrix I J ℂ →L[ℂ] EuclideanSpace ℂ I :=
  ({ toFun := fun a ↦ matrixAmplitudeColumn a j
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } : Matrix I J ℂ →ₗ[ℂ] EuclideanSpace ℂ I).mkContinuous 1
    (fun a ↦ by
      change ‖matrixAmplitudeColumn a j‖ ≤ 1 * ‖a‖
      rw [one_mul]
      exact norm_matrixAmplitudeColumn_le a j)

/-- The Frobenius square is the sum of the actual Euclidean column squares
(`app:ch_osc:eq:osc-normal-basic`). -/
theorem sum_norm_matrixAmplitudeColumn_sq (a : Matrix I J ℂ) :
    ∑ j, ‖matrixAmplitudeColumn a j‖ ^ 2 = ‖a‖ ^ 2 := by
  have h : ‖WithLp.toLp 2 (fun j : J ↦ WithLp.toLp 2 (fun i : I ↦ a i j))‖ ^ 2 =
      ∑ j, ‖matrixAmplitudeColumn a j‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  change ‖a.transpose‖ ^ 2 = ∑ j, ‖matrixAmplitudeColumn a j‖ ^ 2 at h
  simpa only [Matrix.frobenius_norm_transpose] using h.symm

end JanetCartan.NormalComparison
