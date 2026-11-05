module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Hermitian
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Hermitian
public import JanetCartan.Analysis.Operator.WeightedFamily

/-!
# Frobenius bounds for the current mean tensor

The pointwise matrix estimate used by `MeanRecurrence.finite_mean_bounds`,
from `main:lem:mean-recurrence`. All constants are independent of the finite
sample count, and zero weights are allowed.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius
open Matrix

namespace JanetCartan.CurrentMean

variable {m n ι Ω : Type*} [Fintype m] [Fintype n] [Fintype ι]

/-- `main:lem:mean-recurrence`: symmetrization contracts the Frobenius norm. -/
theorem norm_matrixSymmetricPart_le (A : Matrix n n ℝ) :
    ‖matrixSymmetricPart A‖ ≤ ‖A‖ := by
  rw [matrixSymmetricPart, norm_smul]
  calc
    _ ≤ ‖(2 : ℝ)⁻¹‖ * (‖A‖ + ‖Aᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖A‖ := by rw [Matrix.frobenius_norm_transpose]; norm_num; ring

/-- `main:lem:mean-recurrence`: the actual Hermitian polarization has
bilinear constant one in Frobenius norms. -/
theorem norm_mixedHermitianTensor_le (D E : Matrix m n ℂ) :
    ‖mixedHermitianTensor D E‖ ≤ ‖D‖ * ‖E‖ := by
  rw [mixedHermitianTensor_eq_symmetricPart]
  exact (norm_matrixSymmetricPart_le _).trans
    ((frobenius_norm_re_le _).trans (by
      simpa only [Matrix.frobenius_norm_conjTranspose] using
        Matrix.frobenius_norm_mul Dᴴ E))

/-- `main:lem:mean-recurrence`: the continuous bilinear realization of the
existing algebraic polarization, for subsequent Leibniz estimates. -/
def hermitianContinuousBilinear :
    Matrix m n ℂ →L[ℝ] Matrix m n ℂ →L[ℝ] Matrix n n ℝ :=
  (hermitianBilinear (m := m) (n := n)).mkContinuous₂ 1
    (fun D E ↦ by simpa only [one_mul, hermitianBilinear, LinearMap.mk₂_apply] using
      norm_mixedHermitianTensor_le D E)

/-- `main:lem:mean-recurrence`: the continuous realization uses precisely
the tensor in the current recurrence. -/
@[simp] theorem hermitianContinuousBilinear_apply (D E : Matrix m n ℂ) :
    hermitianContinuousBilinear D E = mixedHermitianTensor D E := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: no dimension or sample-count loss is
introduced by passing to the continuous bilinear map. -/
theorem norm_hermitianContinuousBilinear_le :
    ‖hermitianContinuousBilinear (m := m) (n := n)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- `main:lem:mean-recurrence`: weighted pointwise Cauchy–Schwarz for the
actual finite Hermitian family, without division by sample weights. -/
theorem norm_weightedHermitianBilinear_sq_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D E : Ω → ι → Matrix m n ℂ) (x : Ω) :
    ‖weightedHermitianBilinear μ D E x‖ ^ 2 ≤
      (∑ i, μ i * ‖D x i‖ ^ 2) * ∑ i, μ i * ‖E x i‖ ^ 2 := by
  have h : ‖weightedHermitianBilinear μ D E x‖ ≤
      ∑ i, μ i * ‖D x i‖ * ‖E x i‖ := by
    apply (WeightedFamily.norm_sum_weight_smul_le Finset.univ μ
      (fun i _ ↦ hμ i) (fun i ↦ mixedHermitianTensor (D x i) (E x i))).trans
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (norm_mixedHermitianTensor_le (D x i) (E x i)) (hμ i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (WeightedFamily.sum_weight_mul_sq_le Finset.univ μ (fun i _ ↦ hμ i)
      (fun i ↦ ‖D x i‖) (fun i ↦ ‖E x i‖))

end JanetCartan.CurrentMean
