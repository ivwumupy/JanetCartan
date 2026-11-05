module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Analysis.Matrix.HermitianTensor

/-!
# Algebra of leading wave tensors

Pointwise identities from `app:ch_waves:thm:leading`. These apply to arbitrary
real covectors and normal amplitudes; construction of the transported amplitude
and uniform geometric gaps is separate. All matrix norms are Frobenius norms.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius
open Matrix

namespace JanetCartan.LeadingWave

/-- The tensor `ξ ⊙ b` in `app:ch_waves:eq:arbitrary-b-amplitudes`. -/
def symmetricProduct {n : ℕ} (ξ b : Euclidean n) : MetricTensor n :=
  fun i j ↦ (ξ i * b j + b i * ξ j) / 2

/-- Symmetry of the principal covariant derivative tensor in
`app:ch_waves:eq:arbitrary-b-amplitudes`. -/
theorem symmetricProduct_isSymm {n : ℕ} (ξ b : Euclidean n) :
    (symmetricProduct ξ b).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, symmetricProduct]
  ring

/-- Homogeneity in the amplitude in `app:ch_waves:thm:leading`. -/
theorem symmetricProduct_smul_right {n : ℕ} (ξ b : Euclidean n) (a : ℝ) :
    symmetricProduct ξ (a • b) = a • symmetricProduct ξ b := by
  ext i j
  simp only [symmetricProduct, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- The exact squared Frobenius norm behind the lower bound in the proof of
`app:ch_waves:thm:leading`. -/
theorem symmetricProduct_norm_sq {n : ℕ} (ξ b : Euclidean n) :
    ‖symmetricProduct ξ b‖ ^ 2 =
      (‖ξ‖ ^ 2 * ‖b‖ ^ 2 + (∑ i, ξ i * b i) ^ 2) / 2 := by
  have hn : ∀ A : MetricTensor n, ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
    intro A
    have he : ‖A‖ = Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := by
      rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
      simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [he, Real.sq_sqrt (by positivity)]
  rw [hn, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ∑ j, ((ξ i * b j + b i * ξ j) / 2) ^ 2) = _
  have he (i j : Fin n) : ((ξ i * b j + b i * ξ j) / 2) ^ 2 =
      (ξ i ^ 2 * b j ^ 2 + b i ^ 2 * ξ j ^ 2 +
        2 * (ξ i * b i) * (ξ j * b j)) / 4 := by ring
  simp_rw [he, ← Finset.sum_div, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  ring

/-- The lower bound used in `app:ch_waves:thm:leading`, with its exact factor `1/2`. -/
theorem symmetricProduct_norm_sq_lower {n : ℕ} (ξ b : Euclidean n) :
    ‖ξ‖ ^ 2 * ‖b‖ ^ 2 / 2 ≤ ‖symmetricProduct ξ b‖ ^ 2 := by
  rw [symmetricProduct_norm_sq]
  nlinarith [sq_nonneg (∑ i, ξ i * b i)]

/-- Nonzero phase and amplitude give a nonzero tensor in
`app:ch_waves:thm:leading`. -/
theorem symmetricProduct_ne_zero {n : ℕ} {ξ b : Euclidean n}
    (hξ : ξ ≠ 0) (hb : b ≠ 0) : symmetricProduct ξ b ≠ 0 := by
  intro h
  have hl := symmetricProduct_norm_sq_lower ξ b
  rw [h, norm_zero, zero_pow (by decide)] at hl
  have hp : 0 < ‖ξ‖ ^ 2 * ‖b‖ ^ 2 / 2 := by
    exact div_pos (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hξ))
      (sq_pos_of_pos (norm_pos_iff.mpr hb))) (by norm_num)
  exact (not_lt_of_ge hl) hp

/-- Transfer of the phase and amplitude gaps through the equation
`B_G* ν = ξ ⊙ b` in the proof of `app:ch_waves:thm:leading`. This pointwise
estimate retains the pairing identity and the three quantitative bounds as inputs;
it does not construct the geometric inverse or the characteristic gaps. -/
theorem normalAmplitude_norm_lower_of_pairing {n N : ℕ}
    (Q : Euclidean N →ₗ[ℝ] MetricTensor n) {ν : Euclidean N} {ξ b : Euclidean n}
    (hpair : Q ν = symmetricProduct ξ b) {cξ cb C : ℝ}
    (hcξ : 0 < cξ) (hcb : 0 < cb) (hC : 0 < C)
    (hξ : cξ ≤ ‖ξ‖) (hb : cb ≤ ‖b‖) (hQ : ∀ v, ‖Q v‖ ≤ C * ‖v‖) :
    0 < cξ * cb / (2 * C) ∧ cξ * cb / (2 * C) ≤ ‖ν‖ := by
  have hlo := symmetricProduct_norm_sq_lower ξ b
  have hprod : ‖ξ‖ * ‖b‖ ≤ 2 * ‖symmetricProduct ξ b‖ := by
    have hp : 0 ≤ ‖ξ‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hn := norm_nonneg (symmetricProduct ξ b)
    nlinarith [sq_nonneg (‖ξ‖ * ‖b‖ - ‖symmetricProduct ξ b‖)]
  have hupper : ‖symmetricProduct ξ b‖ ≤ C * ‖ν‖ := by
    rw [← hpair]
    exact hQ ν
  have hgap : cξ * cb ≤ ‖ξ‖ * ‖b‖ :=
    mul_le_mul hξ hb hcb.le (norm_nonneg _)
  constructor
  · exact div_pos (mul_pos hcξ hcb) (mul_pos (by norm_num) hC)
  · apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
    nlinarith

/-- The principal ambient derivative `A₀ = -ν ⊗ ξ` in
`app:ch_waves:eq:arbitrary-b-amplitudes`. -/
def principalMatrix {n N : ℕ} (ν : Euclidean N) (ξ : Euclidean n) :
    Matrix (Fin N) (Fin n) ℝ := fun a i ↦ -(ν a * ξ i)

/-- The exact rank-one tensor formula in `app:ch_waves:thm:leading`. -/
theorem principalMatrix_transpose_mul {n N : ℕ} (ν : Euclidean N) (ξ : Euclidean n) :
    (principalMatrix ν ξ)ᵀ * principalMatrix ν ξ =
      fun i j ↦ ‖ν‖ ^ 2 * ξ i * ξ j := by
  ext i j
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, principalMatrix,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Complex Hermitian form of the rank-one identity in
`app:ch_waves:thm:leading` for the real principal amplitude. -/
theorem principalMatrix_hermitianTensor {n N : ℕ} (ν : Euclidean N) (ξ : Euclidean n) :
    hermitianTensor ((principalMatrix ν ξ).map Complex.ofReal) =
      fun i j ↦ ‖ν‖ ^ 2 * ξ i * ξ j := by
  rw [hermitianTensor_ofReal, principalMatrix_transpose_mul]

/-- The tensor scales by the initial density, rather than the initial amplitude,
as asserted in `app:ch_waves:thm:leading`. -/
theorem principalMatrix_density_scaling {n N : ℕ} (ν : Euclidean N)
    (ξ : Euclidean n) (a : ℝ) :
    (principalMatrix (a • ν) ξ)ᵀ * principalMatrix (a • ν) ξ =
      a ^ 2 • ((principalMatrix ν ξ)ᵀ * principalMatrix ν ξ) := by
  rw [principalMatrix_transpose_mul, principalMatrix_transpose_mul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ext i j
  change a ^ 2 * ‖ν‖ ^ 2 * ξ i * ξ j = a ^ 2 * (‖ν‖ ^ 2 * ξ i * ξ j)
  ring

end JanetCartan.LeadingWave
