module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns.Basic

/-!
# The original source weight on every matrix column

The scalar source operator in `app:ch_osc:eq:osc-normal-mask` acts diagonally
on the native finite vector-valued L² input. Its weighted normal is exactly
the sum of the weighted normals of the same scalar columns.
-/

@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap

namespace JanetCartan.NormalComparison

variable {X J : Type*} [MeasurableSpace X] [Fintype J]

/-- Apply the same original scalar source operator to each coordinate of the
native matrix input (`app:ch_osc:eq:osc-normal-mask`). -/
def matrixColumnDiagonal (μ : Measure X) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp (EuclideanSpace ℂ J) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ J) 2 μ :=
  (Pseudodifferential.finiteL2CoordinateIsometry (I := J) μ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : J ↦ Lp ℂ 2 μ)).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j ↦
        M ∘L PiLp.proj (𝕜 := ℂ) 2 (fun _ : J ↦ Lp ℂ 2 μ) j) ∘L
          (Pseudodifferential.finiteL2CoordinateIsometry (I := J) μ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Exact coordinate action of the same source operator
(`app:ch_osc:eq:osc-normal-mask`). -/
theorem matrixColumnDiagonal_coordinate (μ : Measure X)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : Lp (EuclideanSpace ℂ J) 2 μ) (j : J) :
    Pseudodifferential.finiteL2CoordinateIsometry μ (matrixColumnDiagonal μ M f) j =
      M (Pseudodifferential.finiteL2CoordinateIsometry μ f j) := by
  simp [matrixColumnDiagonal]

/-- A genuine scalar multiplication operator becomes literal componentwise
multiplication, with the original measurable symbol and measure
(`app:ch_osc:eq:osc-normal-mask`). -/
theorem matrixColumnDiagonal_ae_smul (μ : Measure X)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (m : X → ℂ)
    (hM : ∀ g : Lp ℂ 2 μ, M g =ᵐ[μ] fun x ↦ m x * g x)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) :
    matrixColumnDiagonal μ M f =ᵐ[μ] fun x ↦ m x • f x := by
  apply (Pseudodifferential.finiteL2CoordinateIsometry_ae_iff μ _ _).mpr
  intro j
  rw [matrixColumnDiagonal_coordinate]
  filter_upwards [hM (Pseudodifferential.finiteL2CoordinateIsometry μ f j),
    Pseudodifferential.finiteL2Coordinates_apply_ae μ f j] with x hx hy
  change Pseudodifferential.finiteL2CoordinateIsometry μ f j x = f x j at hy
  simpa only [PiLp.smul_apply, smul_eq_mul, hy] using hx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Continuity estimates for the original column normals transfer to the
actual matrix normal (`app:ch_osc:prop:osc-normal`). -/
theorem norm_normal_matrixColumnOperator_sub_le (μ : Measure X)
    (T S : J → Lp ℂ 2 μ →L[ℂ] F) {b : J → ℝ}
    (hTS : ∀ j, ‖NormalPerturbation.normal (T j) - NormalPerturbation.normal (S j)‖ ≤ b j) :
    ‖NormalPerturbation.normal (matrixColumnOperator μ T) -
      NormalPerturbation.normal (matrixColumnOperator μ S)‖ ≤ ∑ j, b j := by
  rw [normal_matrixColumnOperator, normal_matrixColumnOperator, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hTS j)

/-- The literal weighted normal of the native matrix-input operator is the
sum of the original weighted scalar-column normals
(`app:ch_osc:eq:osc-normal-mask`). -/
theorem weighted_normal_matrixColumnOperator (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    matrixColumnOperator μ T ∘L matrixColumnDiagonal μ M ∘L
        (matrixColumnOperator μ T).adjoint =
      ∑ j, T j ∘L M ∘L (T j).adjoint := by
  ext g
  simp only [comp_apply, matrixColumnOperator_apply, matrixColumnDiagonal_coordinate,
    matrixColumnOperator_adjoint_coordinate, sum_apply]

/-- Original scalar weighted-normal differences transfer to the actual
matrix family without selecting a new source weight
(`app:ch_osc:eq:osc-normal-mask`). -/
theorem norm_weighted_normal_matrixColumnOperator_sub_le (μ : Measure X)
    (T S : J → Lp ℂ 2 μ →L[ℂ] F) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {b : J → ℝ}
    (hTS : ∀ j, ‖T j ∘L M ∘L (T j).adjoint - S j ∘L M ∘L (S j).adjoint‖ ≤ b j) :
    ‖matrixColumnOperator μ T ∘L matrixColumnDiagonal μ M ∘L
          (matrixColumnOperator μ T).adjoint -
        matrixColumnOperator μ S ∘L matrixColumnDiagonal μ M ∘L
          (matrixColumnOperator μ S).adjoint‖ ≤ ∑ j, b j := by
  rw [weighted_normal_matrixColumnOperator, weighted_normal_matrixColumnOperator,
    ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hTS j)

/-- The matrix weighted-normal comparison loses only the fixed input
dimension (`app:ch_osc:eq:osc-normal-mask`). -/
theorem norm_weighted_normal_matrixColumnOperator_sub_le_of_uniform_bound (μ : Measure X)
    (T S : J → Lp ℂ 2 μ →L[ℂ] F) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {B : ℝ}
    (hTS : ∀ j, ‖T j ∘L M ∘L (T j).adjoint - S j ∘L M ∘L (S j).adjoint‖ ≤ B) :
    ‖matrixColumnOperator μ T ∘L matrixColumnDiagonal μ M ∘L
          (matrixColumnOperator μ T).adjoint -
        matrixColumnOperator μ S ∘L matrixColumnDiagonal μ M ∘L
          (matrixColumnOperator μ S).adjoint‖ ≤ (Fintype.card J : ℝ) * B := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    norm_weighted_normal_matrixColumnOperator_sub_le μ T S M hTS

end JanetCartan.NormalComparison
