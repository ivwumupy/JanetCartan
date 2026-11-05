module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.LinearAlgebra.GramProjection

/-!
# Frobenius reconstruction in a stress frame

The tensor specialization of the inverse-Gram formula in
`main:eq:completion-error` and `app:ch_response:eq:response-full-identity`.
The scoped inner product below induces the existing Frobenius matrix norm.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

namespace TensorFrobenius

/-- The Frobenius contraction in `main:eq:reduced-convention`, compatible with
exactly the matrix norm already used for metric fields. -/
scoped instance metricTensorInnerProductSpace (n : ℕ) :
    InnerProductSpace ℝ (MetricTensor n) where
  inner := tensorPairing
  norm_sq_eq_re_inner A := by
    change ‖A‖ ^ 2 = tensorPairing A A
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt (by positivity)]
    simp only [Real.rpow_two, Real.norm_eq_abs]
    simp only [sq_abs, tensorPairing, ← pow_two]
  conj_inner_symm A B := by
    simp [tensorPairing, mul_comm]
  add_left A B C := by
    simp [tensorPairing, add_mul, Finset.sum_add_distrib]
  smul_left A B c := by
    simp [tensorPairing, mul_assoc, Finset.mul_sum]

end TensorFrobenius

open scoped TensorFrobenius

/-- The matrix `Gram_G = (Q_i : Q_j)` in
`app:ch_response:prop:response-ambient`. -/
def stressGram {n : ℕ} {ι : Type*} (Q : ι → MetricTensor n) : Matrix ι ι ℝ :=
  fun i j ↦ tensorPairing (Q i) (Q j)

/-- The tensor Gram matrix is the Hilbert-space Gram matrix, with no change of
normalization (`main:eq:completion-error`). -/
theorem stressGram_eq_gram {n : ℕ} {ι : Type*} (Q : ι → MetricTensor n) :
    stressGram Q = Matrix.gram ℝ Q := rfl

/-- Reconstruction from actual Frobenius contractions in
`main:eq:completion-error`. -/
theorem tensor_eq_inverseGram_of_mem_span {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {Q : ι → MetricTensor n}
    (hQ : LinearIndependent ℝ Q) {H : MetricTensor n}
    (hH : H ∈ Submodule.span ℝ (Set.range Q)) :
    H = ∑ i, ∑ j, ((stressGram Q)⁻¹ i j * tensorPairing (Q j) H) • Q i :=
  eq_sum_inverseGram_of_mem_span hQ hH

/-- In a basis of the actual stress space, the full tensor is determined by
its contractions (`main:eq:completion-error`). -/
theorem stressTensor_eq_inverseGram {n N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {F : Euclidean n → Euclidean N} {x : Euclidean n}
    {Q : ι → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x)
    {H : MetricTensor n} (hH : H ∈ stressSpace F x) :
    H = ∑ i, ∑ j, ((stressGram Q)⁻¹ i j * tensorPairing (Q j) H) • Q i :=
  tensor_eq_inverseGram_of_mem_span hQ (by rw [← hspan] at hH; exact hH)

end JanetCartan
