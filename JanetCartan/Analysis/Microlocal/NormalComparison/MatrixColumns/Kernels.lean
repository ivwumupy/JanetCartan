module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Literal kernels of the same matrix columns

The finite sum in `app:ch_osc:prop:osc-normal` is moved inside the original
kernel integral using the integrability of each original column.  The
result is multiplication by the same rectangular matrix, and its source
normal amplitude is the sum of the original column outer products.
-/

@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap Filter

namespace JanetCartan.NormalComparison

variable {X Y J F : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype J]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace Y] [CompleteSpace F] in
/-- The actual vector L² input gives integrable original column kernels;
only the representative is changed by coordinate extraction
(`app:ch_osc:prop:osc-normal`). -/
theorem integrable_matrixColumnIntegrand (μ : Measure X)
    (K : J → Y → X → F)
    (hK : ∀ j (g : Lp ℂ 2 μ) y, Integrable (fun x ↦ g x • K j y x) μ)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) (j : J) (y : Y) :
    Integrable (fun x ↦ f x j • K j y x) μ := by
  apply (hK j (Pseudodifferential.finiteL2CoordinateIsometry μ f j) y).congr
  filter_upwards [Pseudodifferential.finiteL2Coordinates_apply_ae μ f j] with x hx
  change Pseudodifferential.finiteL2CoordinateIsometry μ f j x = f x j at hx
  rw [hx]

/-- Literal matrix-kernel reassembly on the whole native vector input.
The integrability hypotheses are supplied by the original scalar-column
constructors, not by a proposed matrix output
(`app:ch_osc:prop:osc-normal`). -/
theorem matrixColumnOperator_ae_integral (μ : Measure X) (ν : Measure Y)
    (T : J → Lp ℂ 2 μ →L[ℂ] Lp F 2 ν) (K : J → Y → X → F)
    (hT : ∀ j (g : Lp ℂ 2 μ), T j g =ᵐ[ν] fun y ↦ ∫ x, g x • K j y x ∂μ)
    (hK : ∀ j (g : Lp ℂ 2 μ) y, Integrable (fun x ↦ g x • K j y x) μ)
    (f : Lp (EuclideanSpace ℂ J) 2 μ) :
    matrixColumnOperator μ T f =ᵐ[ν] fun y ↦ ∫ x, ∑ j, f x j • K j y x ∂μ := by
  rw [matrixColumnOperator_apply]
  have hall := ae_all_iff.mpr (fun j ↦
    hT j (Pseudodifferential.finiteL2CoordinateIsometry μ f j))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j ↦ T j (Pseudodifferential.finiteL2CoordinateIsometry μ f j)), hall] with y hy hty
  rw [hy, integral_finsetSum _ (fun j _ ↦ integrable_matrixColumnIntegrand μ K hK f j y)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hty j]
  apply integral_congr_ae
  filter_upwards [Pseudodifferential.finiteL2Coordinates_apply_ae μ f j] with x hx
  change Pseudodifferential.finiteL2CoordinateIsometry μ f j x = f x j at hx
  rw [hx]

end JanetCartan.NormalComparison

namespace JanetCartan.NormalComparison

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The original Euclidean column of a rectangular amplitude
(`app:ch_osc:prop:osc-normal`). -/
def matrixAmplitudeColumn (a : Matrix I J ℂ) (j : J) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i ↦ a i j)

omit [Fintype I] in
/-- The finite column action is literal multiplication by the same matrix
(`app:ch_osc:prop:osc-normal`). -/
theorem sum_smul_matrixAmplitudeColumn (a : Matrix I J ℂ) (v : EuclideanSpace ℂ J) :
    ∑ j, v j • matrixAmplitudeColumn a j = WithLp.toLp 2 (a.mulVec v.ofLp) := by
  ext i
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, matrixAmplitudeColumn,
    smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [Fintype I] in
/-- The exact rectangular source-normal amplitude is the sum of the original
column outer products; the two physical arguments may differ
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem matrix_mul_conjTranspose_eq_sum_columns (a b : Matrix I J ℂ) :
    a * b.conjTranspose =
      ∑ j, fun i i' ↦ matrixAmplitudeColumn a j i * star (matrixAmplitudeColumn b j i') := by
  ext i i'
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, matrixAmplitudeColumn]

end JanetCartan.NormalComparison
