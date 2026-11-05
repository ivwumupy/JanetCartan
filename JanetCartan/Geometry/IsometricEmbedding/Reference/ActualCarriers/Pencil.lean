module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.DeterminantDeriv

/-!
# The pencil of a current stress frame

The pointwise definitions `M_F`, `p_F`, and `q_F` of
`app:ch_seed:setup:seed-current`. The frame is an argument: this module does not
construct the projected frame or assume that it has the desired carrier menu.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

/-- The current pencil has row `(Qᵢ ξ)ᵀ`
(`app:ch_seed:setup:seed-current`). -/
def pencil {n : ℕ} (Q : Fin n → MetricTensor n) (ξ : Euclidean n) : MetricTensor n :=
  fun i j ↦ ∑ k, Q i j k * ξ k

/-- The current characteristic polynomial (`app:ch_seed:setup:seed-current`). -/
def determinant {n : ℕ} (Q : Fin n → MetricTensor n) (ξ : Euclidean n) : ℝ :=
  (pencil Q ξ).det

/-- The current quadratic stress contraction (`app:ch_seed:setup:seed-current`). -/
def quadratic {n : ℕ} (Q : Fin n → MetricTensor n) (ξ : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 fun i ↦ ∑ j, ∑ k, ξ j * Q i j k * ξ k

/-- The pencil applied to its covector is the quadratic contraction
(`app:ch_seed:setup:seed-current`). -/
theorem pencil_mulVec_self {n : ℕ} (Q : Fin n → MetricTensor n) (ξ : Euclidean n)
    (i : Fin n) :
    (pencil Q ξ *ᵥ (fun j ↦ ξ j)) i = quadratic Q ξ i := by
  simp only [pencil, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change Q i j k * ξ k * ξ j = ξ j * Q i j k * ξ k
  ring

/-- The current pencil specializes exactly to the existing frozen pencil
(`app:ch_seed:setup:seed-current`). -/
@[simp] theorem pencil_cubeStress {n : ℕ} (ξ : Euclidean n) :
    pencil (cubeStress n) ξ = cubePencil ξ := by
  ext i j
  simp only [pencil, cubeStress, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, ite_and, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, cubePencil]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The current characteristic polynomial specializes to `p₀`
(`app:ch_seed:setup:seed-current`). -/
@[simp] theorem determinant_cubeStress {n : ℕ} (ξ : Euclidean n) :
    determinant (cubeStress n) ξ = cubeDeterminant ξ := by
  simp [determinant, cubeDeterminant]

/-- Compatibility with the existing frozen quadratic contraction
(`app:ch_seed:setup:seed-current`). -/
@[simp] theorem quadratic_cubeStress {n : ℕ} (ξ : Euclidean n) :
    quadratic (cubeStress n) ξ = cubeQuadraticContraction ξ := rfl

/-- The covector dependence of the current pencil is linear, with Frobenius
matrix norm (`app:ch_seed:setup:seed-current`). -/
def pencilContinuousLinearMap {n : ℕ} (Q : Fin n → MetricTensor n) :
    Euclidean n →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap {
    toFun := pencil Q
    map_add' := by
      intro ξ η
      ext i j
      simp [pencil, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a ξ
      ext i j
      simp [pencil, Finset.mul_sum, mul_left_comm] }

/-- Evaluation of the bundled current pencil
(`app:ch_seed:setup:seed-current`). -/
@[simp] theorem pencilContinuousLinearMap_apply {n : ℕ}
    (Q : Fin n → MetricTensor n) (ξ : Euclidean n) :
    pencilContinuousLinearMap Q ξ = pencil Q ξ := rfl

/-- Jacobi's formula and the chain rule for the current determinant, including
its characteristic set (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem hasFDerivAt_determinant {n : ℕ} (Q : Fin n → MetricTensor n) (ξ : Euclidean n) :
    HasFDerivAt (determinant Q)
      ((fderiv ℝ Matrix.det (pencil Q ξ)).comp (pencilContinuousLinearMap Q)) ξ :=
  (Matrix.differentiable_det (pencil Q ξ)).hasFDerivAt.comp ξ
    ((pencilContinuousLinearMap Q).hasFDerivAt (x := ξ))

/-- The current determinant differential expressed using its adjugate
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem fderiv_determinant_apply {n : ℕ} (Q : Fin n → MetricTensor n)
    (ξ η : Euclidean n) :
    fderiv ℝ (determinant Q) ξ η = ((pencil Q ξ).adjugate * pencil Q η).trace := by
  rw [(hasFDerivAt_determinant Q ξ).fderiv, ContinuousLinearMap.comp_apply,
    pencilContinuousLinearMap_apply, Matrix.fderiv_det_apply]

end JanetCartan.ActualCarriers
