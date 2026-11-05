module

public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Real and complex quadratic tensors

Algebraic identities for finite ambient derivative matrices, from
`app:ch_pairs:lem:pairs-ledger` and `app:ch_mean_pairs:eq:mean-exact-self-change`
in `paper.tex`. The row index is the ambient coordinate and the column index is
the domain coordinate. Ordinary transpose defines the symmetric bilinear tensor;
conjugate transpose defines the Hermitian self tensor.

These identities have no analytic hypotheses. The ordered signed expansion and
analytic product corrections are assembled in separate modules.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate
open Matrix

namespace JanetCartan

variable {m n 𝕜 : Type*} [Fintype m] [Field 𝕜]

/-- The ordinary symmetric part, used in app:ch_mean_pairs:eq:mean-exact-self-change. -/
def matrixSymmetricPart {ι : Type*} (A : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  (2 : 𝕜)⁻¹ • (A + Aᵀ)

/-- The bilinear tensor `𝔅(D,E) = (DᵀE + EᵀD)/2` of app:ch_pairs:lem:pairs-ledger.
The transpose here is ordinary, even for complex matrices. -/
def symmetricBilinearTensor (D E : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (2 : 𝕜)⁻¹ • (Dᵀ * E + Eᵀ * D)

/-- Coordinate formula for the tensor in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_apply (D E : Matrix m n 𝕜) (i j : n) :
    symmetricBilinearTensor D E i j =
      ∑ k, (2 : 𝕜)⁻¹ * (D k i * E k j + E k i * D k j) := by
  simp only [symmetricBilinearTensor, Matrix.smul_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]

/-- Symmetry in the two inputs of the tensor in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_comm (D E : Matrix m n 𝕜) :
    symmetricBilinearTensor D E = symmetricBilinearTensor E D := by
  simp only [symmetricBilinearTensor, add_comm]

/-- The tensor in app:ch_pairs:lem:pairs-ledger is a symmetric matrix. -/
theorem symmetricBilinearTensor_isSymm (D E : Matrix m n 𝕜) :
    (symmetricBilinearTensor D E).IsSymm := by
  simp [Matrix.IsSymm, symmetricBilinearTensor, Matrix.transpose_mul, add_comm]

/-- The tensor in app:ch_pairs:lem:pairs-ledger is the symmetric part of `DᵀE`. -/
theorem symmetricBilinearTensor_eq_symmetricPart (D E : Matrix m n 𝕜) :
    symmetricBilinearTensor D E = matrixSymmetricPart (Dᵀ * E) := by
  simp [symmetricBilinearTensor, matrixSymmetricPart, Matrix.transpose_mul]

/-- The ordinary quadratic diagonal of app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_self [CharZero 𝕜] (D : Matrix m n 𝕜) :
    symmetricBilinearTensor D D = Dᵀ * D := by
  ext i j
  simp only [symmetricBilinearTensor, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- Left additivity for the ordered expansion in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_add_left (D E F : Matrix m n 𝕜) :
    symmetricBilinearTensor (D + E) F =
      symmetricBilinearTensor D F + symmetricBilinearTensor E F := by
  ext i j
  simp only [symmetricBilinearTensor_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Right additivity for the ordered expansion in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_add_right (D E F : Matrix m n 𝕜) :
    symmetricBilinearTensor D (E + F) =
      symmetricBilinearTensor D E + symmetricBilinearTensor D F := by
  rw [symmetricBilinearTensor_comm, symmetricBilinearTensor_add_left]
  simp only [symmetricBilinearTensor_comm]

/-- Left homogeneity for the physical coefficients in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_smul_left (c : 𝕜) (D E : Matrix m n 𝕜) :
    symmetricBilinearTensor (c • D) E = c • symmetricBilinearTensor D E := by
  ext i j
  simp only [symmetricBilinearTensor_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Right homogeneity for the physical coefficients in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_smul_right (c : 𝕜) (D E : Matrix m n 𝕜) :
    symmetricBilinearTensor D (c • E) = c • symmetricBilinearTensor D E := by
  rw [symmetricBilinearTensor_comm, symmetricBilinearTensor_smul_left,
    symmetricBilinearTensor_comm]

/-- The zero left input in the expansion of app:ch_pairs:lem:pairs-ledger. -/
@[simp] theorem symmetricBilinearTensor_zero_left (D : Matrix m n 𝕜) :
    symmetricBilinearTensor 0 D = 0 := by
  simp [symmetricBilinearTensor]

/-- The zero right input in the expansion of app:ch_pairs:lem:pairs-ledger. -/
@[simp] theorem symmetricBilinearTensor_zero_right (D : Matrix m n 𝕜) :
    symmetricBilinearTensor D 0 = 0 := by
  simp [symmetricBilinearTensor]

/-- Left finite-sum expansion for app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_sum_left {ι : Type*} (s : Finset ι)
    (D : ι → Matrix m n 𝕜) (E : Matrix m n 𝕜) :
    symmetricBilinearTensor (∑ a ∈ s, D a) E = ∑ a ∈ s, symmetricBilinearTensor (D a) E := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha hs => simp [ha, hs, symmetricBilinearTensor_add_left]

/-- Right finite-sum expansion for app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_sum_right {ι : Type*} (s : Finset ι)
    (D : Matrix m n 𝕜) (E : ι → Matrix m n 𝕜) :
    symmetricBilinearTensor D (∑ a ∈ s, E a) = ∑ a ∈ s, symmetricBilinearTensor D (E a) := by
  simp only [symmetricBilinearTensor_comm D, symmetricBilinearTensor_sum_left]

/-- Exact bilinear quadratic expansion underlying app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_add_self (B D : Matrix m n 𝕜) :
    symmetricBilinearTensor (B + D) (B + D) =
      symmetricBilinearTensor B B + (2 : 𝕜) • symmetricBilinearTensor B D +
        symmetricBilinearTensor D D := by
  rw [symmetricBilinearTensor_add_left, symmetricBilinearTensor_add_right,
    symmetricBilinearTensor_add_right, symmetricBilinearTensor_comm D B]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Exact ordinary quadratic increment underlying app:ch_pairs:lem:pairs-ledger. -/
theorem transpose_mul_add_sub [CharZero 𝕜] (B D : Matrix m n 𝕜) :
    (B + D)ᵀ * (B + D) - Bᵀ * B = (2 : 𝕜) • symmetricBilinearTensor B D + Dᵀ * D := by
  rw [← symmetricBilinearTensor_self (B + D), symmetricBilinearTensor_add_self,
    symmetricBilinearTensor_self B, symmetricBilinearTensor_self D]
  abel

/-- Conjugation of both inputs in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_conj (D E : Matrix m n ℂ) :
    symmetricBilinearTensor (D.map conj) (E.map conj) =
      (symmetricBilinearTensor D E).map conj := by
  ext i j
  simp [symmetricBilinearTensor_apply, map_sum, map_ofNat]

/-- Compatibility of real and complex tensors in app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_ofReal (D E : Matrix m n ℝ) :
    symmetricBilinearTensor (D.map Complex.ofReal) (E.map Complex.ofReal) =
      (symmetricBilinearTensor D E).map Complex.ofReal := by
  ext i j
  simp [symmetricBilinearTensor_apply]

/-- The realification identity in the proof of app:ch_pairs:lem:pairs-ledger:
`2 𝔅(Re D, Re E) = Re 𝔅(D,E) + Re 𝔅(D,conj E)`. -/
theorem symmetricBilinearTensor_realification (D E : Matrix m n ℂ) :
    (2 : ℝ) • symmetricBilinearTensor (D.map Complex.re) (E.map Complex.re) =
      (symmetricBilinearTensor D E).map Complex.re +
        (symmetricBilinearTensor D (E.map conj)).map Complex.re := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, symmetricBilinearTensor_apply,
    Matrix.add_apply, Matrix.map_apply, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp [Complex.mul_re, Complex.add_re]
  ring

/-- The complete real Hermitian self tensor `Re(DᴴD)` of
app:ch_pairs:lem:pairs-ledger and app:ch_mean_pairs:eq:mean-exact-self-change. -/
def hermitianTensor (D : Matrix m n ℂ) : Matrix n n ℝ :=
  (Dᴴ * D).map Complex.re

/-- Real coordinate formula for the Hermitian self term of app:ch_pairs:lem:pairs-ledger. -/
theorem hermitianTensor_apply (D : Matrix m n ℂ) (i j : n) :
    hermitianTensor D i j =
      ∑ k, ((D k i).re * (D k j).re + (D k i).im * (D k j).im) := by
  simp [hermitianTensor, Matrix.mul_apply, Complex.mul_re]

/-- Symmetry of the real Hermitian self tensor of app:ch_pairs:lem:pairs-ledger. -/
theorem hermitianTensor_isSymm (D : Matrix m n ℂ) :
    (hermitianTensor D).IsSymm := by
  ext i j
  simp [hermitianTensor_apply, mul_comm]

/-- The Hermitian difference diagonal in app:ch_pairs:lem:pairs-ledger.
The real matrix `Re(DᴴD)` is explicitly included into the complex matrices. -/
theorem symmetricBilinearTensor_conj_self (D : Matrix m n ℂ) :
    symmetricBilinearTensor D (D.map conj) = (hermitianTensor D).map Complex.ofReal := by
  ext i j
  simp only [symmetricBilinearTensor_apply, hermitianTensor, Matrix.map_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Real-valued version of the Hermitian diagonal identity of app:ch_pairs:lem:pairs-ledger. -/
theorem symmetricBilinearTensor_re_conj_self (D : Matrix m n ℂ) :
    (symmetricBilinearTensor D (D.map conj)).map Complex.re = hermitianTensor D := by
  rw [symmetricBilinearTensor_conj_self]
  ext i j
  simp

/-- Conjugation preserves the Hermitian self term of app:ch_pairs:lem:pairs-ledger. -/
theorem hermitianTensor_conj (D : Matrix m n ℂ) :
    hermitianTensor (D.map conj) = hermitianTensor D := by
  ext i j
  simp [hermitianTensor_apply]

/-- For real inputs, the self tensor of app:ch_pairs:lem:pairs-ledger is `DᵀD`. -/
theorem hermitianTensor_ofReal (D : Matrix m n ℝ) :
    hermitianTensor (D.map Complex.ofReal) = Dᵀ * D := by
  ext i j
  simp [hermitianTensor_apply, Matrix.mul_apply]

/-- Scalar factors contribute their squared modulus to the self tensor
of app:ch_pairs:lem:pairs-ledger; in particular unit phases cancel. -/
theorem hermitianTensor_smul (c : ℂ) (D : Matrix m n ℂ) :
    hermitianTensor (c • D) = Complex.normSq c • hermitianTensor D := by
  ext i j
  simp only [hermitianTensor_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Equation app:ch_mean_pairs:eq:mean-exact-self-change, with the ordinary
symmetric part of `Re(BᴴD)` and the complete quadratic remainder. -/
theorem hermitianTensor_add_sub (B D : Matrix m n ℂ) :
    hermitianTensor (B + D) - hermitianTensor B =
      (2 : ℝ) • matrixSymmetricPart ((Bᴴ * D).map Complex.re) + hermitianTensor D := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, hermitianTensor_apply,
    matrixSymmetricPart, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.add_re, Complex.add_im]
  rw [← mul_assoc, mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Additive form of app:ch_mean_pairs:eq:mean-exact-self-change. -/
theorem hermitianTensor_add (B D : Matrix m n ℂ) :
    hermitianTensor (B + D) = hermitianTensor B +
      (2 : ℝ) • matrixSymmetricPart ((Bᴴ * D).map Complex.re) + hermitianTensor D := by
  have h := hermitianTensor_add_sub B D
  exact (sub_eq_iff_eq_add.mp h).trans (by abel)

end JanetCartan
