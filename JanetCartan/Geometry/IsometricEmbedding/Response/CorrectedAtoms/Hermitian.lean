module

public import JanetCartan.Analysis.Matrix.HermitianTensor
public import JanetCartan.Analysis.ContDiff.Norm.Products

/-!
# The bilinear map underlying atomic densities

The real part of the Hermitian product in
`app:ch_response:eq:current-density-lipschitz`, with Frobenius norms.
This is algebra and a product estimate; it does not assume or construct a wave.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius
open Matrix

namespace JanetCartan

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `app:ch_response:eq:current-density-lipschitz`: taking real parts contracts
the Frobenius norm. -/
theorem frobenius_norm_re_le (A : Matrix m n ℂ) : ‖A.map Complex.re‖ ≤ ‖A‖ := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (A i j)) 2

/-- `app:ch_response:eq:current-density-lipschitz`: the real bilinear Hermitian
cross product. Its diagonal is the existing `hermitianTensor`. -/
def hermitianCrossBilinear (m n : Type*) [Fintype m] [Fintype n] :
    Matrix m n ℂ →L[ℝ] Matrix m n ℂ →L[ℝ] Matrix n n ℝ :=
  (LinearMap.mk₂ ℝ (fun (A B : Matrix m n ℂ) ↦ (Aᴴ * B).map Complex.re)
    (by intros; ext i j; simp [Matrix.add_mul])
    (by intros; ext i j; simp [Matrix.smul_mul])
    (by intros; ext i j; simp [Matrix.mul_add])
    (by intros; ext i j; simp [Matrix.mul_smul])).mkContinuous₂ 1
    (fun A B ↦ by
      simpa only [LinearMap.mk₂_apply, one_mul, Matrix.frobenius_norm_conjTranspose]
        using (frobenius_norm_re_le (Aᴴ * B)).trans (Matrix.frobenius_norm_mul Aᴴ B))

/-- The cross product of `app:ch_response:eq:current-density-lipschitz`. -/
@[simp] theorem hermitianCrossBilinear_apply (A B : Matrix m n ℂ) :
    hermitianCrossBilinear m n A B = (Aᴴ * B).map Complex.re := rfl

/-- The diagonal in `app:ch_response:eq:current-density-lipschitz` is exactly
the real Hermitian tensor, with no change of matrix convention. -/
@[simp] theorem hermitianCrossBilinear_self (A : Matrix m n ℂ) :
    hermitianCrossBilinear m n A A = hermitianTensor A := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `app:ch_response:eq:current-density-lipschitz`: the bilinear norm bound
is independent of matrix dimensions. -/
theorem norm_hermitianCrossBilinear_le (m n : Type*) [Fintype m] [Fintype n] :
    ‖hermitianCrossBilinear m n‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end JanetCartan
