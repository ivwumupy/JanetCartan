module

public import JanetCartan.Analysis.Operator.NormalPerturbation.Weighted
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Coordinates

/-!
# Native L² assembly of the matrix columns

The rectangular amplitudes in `app:ch_osc:prop:osc-normal` act on the entire
finite vector-valued L² input.  This is the unit-weight row of the actual
scalar-column operators, conjugated by the coordinate L² isometry for the
same measure.  In particular its normal is the sum of those column normals.
-/

@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap

namespace JanetCartan.NormalComparison

variable {X J F : Type*} [MeasurableSpace X] [Fintype J]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Assemble the actual scalar columns on native vector L², with the original
input measure (`app:ch_osc:prop:osc-normal`). -/
def matrixColumnOperator (μ : Measure X) (T : J → Lp ℂ 2 μ →L[ℂ] F) :
    Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] F :=
  NormalPerturbation.weightedRow (fun _ : J ↦ 1) T ∘L
    (Pseudodifferential.finiteL2CoordinateIsometry (I := J) μ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Literal finite column sum on native vector L²
(`app:ch_osc:prop:osc-normal`). -/
theorem matrixColumnOperator_apply (μ : Measure X) (T : J → Lp ℂ 2 μ →L[ℂ] F)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) :
    matrixColumnOperator μ T f =
      ∑ j, T j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) := by
  simp [matrixColumnOperator, NormalPerturbation.weightedRow_apply]

/-- The native adjoint has precisely the original scalar-column adjoints
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem matrixColumnOperator_adjoint_coordinate (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) (g : F) (j : J) :
    Pseudodifferential.finiteL2CoordinateIsometry μ
      ((matrixColumnOperator μ T).adjoint g) j = (T j).adjoint g := by
  simp [matrixColumnOperator, adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]

/-- The normal of the same native matrix-input operator is the sum of the
scalar-column normals (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem normal_matrixColumnOperator (μ : Measure X) (T : J → Lp ℂ 2 μ →L[ℂ] F) :
    NormalPerturbation.normal (matrixColumnOperator μ T) =
      ∑ j, NormalPerturbation.normal (T j) := by
  ext g
  simp only [NormalPerturbation.normal, comp_apply, matrixColumnOperator_apply,
    matrixColumnOperator_adjoint_coordinate, sum_apply]

/-- Coordinate extraction does not change the norm of the finite row
(`app:ch_osc:eq:osc-normal-basic`). -/
theorem norm_matrixColumnOperator_eq (μ : Measure X) (T : J → Lp ℂ 2 μ →L[ℂ] F) :
    ‖matrixColumnOperator μ T‖ =
      ‖NormalPerturbation.weightedRow (fun _ : J ↦ 1) T‖ :=
  opNorm_comp_linearIsometryEquiv _ (Pseudodifferential.finiteL2CoordinateIsometry (I := J) μ)

/-- Square-sum column norm bound for the native matrix operator
(`app:ch_osc:eq:osc-normal-basic`). -/
theorem norm_matrixColumnOperator_le (μ : Measure X) (T : J → Lp ℂ 2 μ →L[ℂ] F) :
    ‖matrixColumnOperator μ T‖ ≤ Real.sqrt (∑ j, ‖T j‖ ^ 2) := by
  rw [norm_matrixColumnOperator_eq]
  simpa only [one_mul] using NormalPerturbation.norm_weightedRow_le
    (fun _ : J ↦ 1) (fun _ ↦ zero_le_one) T

/-- Supplied bounds for the original columns transfer to their actual matrix
operator (`app:ch_osc:eq:osc-normal-basic`). -/
theorem norm_matrixColumnOperator_le_of_bounds (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) {b : J → ℝ} (hT : ∀ j, ‖T j‖ ≤ b j) :
    ‖matrixColumnOperator μ T‖ ≤ Real.sqrt (∑ j, b j ^ 2) := by
  rw [norm_matrixColumnOperator_eq]
  simpa only [one_mul] using NormalPerturbation.norm_weightedRow_le_of_bounds
    (fun _ : J ↦ 1) (fun _ ↦ zero_le_one) T hT

/-- A common original-column bound incurs only the fixed square root of the
input dimension (`app:ch_osc:eq:osc-normal-basic`). -/
theorem norm_matrixColumnOperator_le_of_uniform_bound (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B) (hT : ∀ j, ‖T j‖ ≤ B) :
    ‖matrixColumnOperator μ T‖ ≤ Real.sqrt (Fintype.card J : ℝ) * B := by
  have h := norm_matrixColumnOperator_le_of_bounds μ T hT
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB] using h

/-- Matrix-column assembly preserves the original perturbation
(`app:ch_osc:prop:osc-normal`). -/
theorem matrixColumnOperator_sub (μ : Measure X) (T S : J → Lp ℂ 2 μ →L[ℂ] F) :
    matrixColumnOperator μ (fun j ↦ T j - S j) =
      matrixColumnOperator μ T - matrixColumnOperator μ S := by
  ext f
  simp only [matrixColumnOperator_apply, sub_apply, Finset.sum_sub_distrib]

/-- Same-phase column differences give the corresponding actual matrix
difference (`app:ch_osc:prop:osc-normal`). -/
theorem norm_matrixColumnOperator_sub_le (μ : Measure X)
    (T S : J → Lp ℂ 2 μ →L[ℂ] F) {b : J → ℝ} (hTS : ∀ j, ‖T j - S j‖ ≤ b j) :
    ‖matrixColumnOperator μ T - matrixColumnOperator μ S‖ ≤ Real.sqrt (∑ j, b j ^ 2) := by
  rw [← matrixColumnOperator_sub]
  exact norm_matrixColumnOperator_le_of_bounds μ _ hTS

/-- Squared column norm estimates, as in the fixed-parameter part of
`app:ch_osc:eq:osc-normal-basic`, sum on the actual native input. -/
theorem norm_matrixColumnOperator_sq_le_of_bounds (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) {b : J → ℝ} (hT : ∀ j, ‖T j‖ ^ 2 ≤ b j) :
    ‖matrixColumnOperator μ T‖ ^ 2 ≤ ∑ j, b j := by
  rw [norm_matrixColumnOperator_eq, ← NormalPerturbation.norm_normal]
  have h := NormalPerturbation.norm_normal_weightedRow_le
    (fun _ : J ↦ 1) (fun _ ↦ zero_le_one) T
  simp only [one_mul] at h
  exact h.trans (Finset.sum_le_sum fun j _ ↦ hT j)

/-- Uniform same-phase perturbations incur only the fixed square root of
the number of input columns (`app:ch_osc:prop:osc-normal`). -/
theorem norm_matrixColumnOperator_sub_le_of_uniform_bound (μ : Measure X)
    (T S : J → Lp ℂ 2 μ →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B)
    (hTS : ∀ j, ‖T j - S j‖ ≤ B) :
    ‖matrixColumnOperator μ T - matrixColumnOperator μ S‖ ≤ Real.sqrt (Fintype.card J : ℝ) * B := by
  rw [← matrixColumnOperator_sub]
  exact norm_matrixColumnOperator_le_of_uniform_bound μ _ hB hTS

end JanetCartan.NormalComparison
