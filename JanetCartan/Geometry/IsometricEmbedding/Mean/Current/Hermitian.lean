module

public import JanetCartan.Analysis.Matrix.HermitianTensor
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The quadratic tensor of a finite current family

The real bilinear map whose diagonal is the weighted Hermitian tensor in
`main:eq:mean-equation` and `app:ch_mean_pairs:eq:mean-exact-self-change`.
The inputs may be actual complex derivative fields on any common domain.
No sampling, regularity, or size estimates are asserted here.
-/

@[expose] public noncomputable section

namespace JanetCartan.CurrentMean

open Matrix

variable {m n : Type*} [Fintype m]

/-- `app:ch_mean_pairs:eq:mean-exact-self-change`: the real symmetric
polarization of `Re(Dᴴ D)`, retaining both real quadratures. -/
def mixedHermitianTensor (D E : Matrix m n ℂ) : Matrix n n ℝ :=
  symmetricBilinearTensor (D.map Complex.re) (E.map Complex.re) +
    symmetricBilinearTensor (D.map Complex.im) (E.map Complex.im)

/-- Symmetry of the polarization in `app:ch_mean_pairs:eq:mean-exact-self-change`. -/
theorem mixedHermitianTensor_comm (D E : Matrix m n ℂ) :
    mixedHermitianTensor D E = mixedHermitianTensor E D := by
  simp only [mixedHermitianTensor, symmetricBilinearTensor_comm]

/-- Left additivity of the tensor in `app:ch_mean_pairs:eq:mean-exact-self-change`. -/
theorem mixedHermitianTensor_add_left (D E F : Matrix m n ℂ) :
    mixedHermitianTensor (D + E) F = mixedHermitianTensor D F + mixedHermitianTensor E F := by
  have hre : (D + E).map Complex.re = D.map Complex.re + E.map Complex.re := by
    ext i j; simp
  have him : (D + E).map Complex.im = D.map Complex.im + E.map Complex.im := by
    ext i j; simp
  simp only [mixedHermitianTensor, hre, him, symmetricBilinearTensor_add_left]
  abel

/-- Real homogeneity of the tensor in `app:ch_mean_pairs:eq:mean-exact-self-change`. -/
theorem mixedHermitianTensor_smul_left (c : ℝ) (D E : Matrix m n ℂ) :
    mixedHermitianTensor (c • D) E = c • mixedHermitianTensor D E := by
  have hre : (c • D).map Complex.re = c • D.map Complex.re := by
    ext i j; simp
  have him : (c • D).map Complex.im = c • D.map Complex.im := by
    ext i j; simp
  simp only [mixedHermitianTensor, hre, him, symmetricBilinearTensor_smul_left, smul_add]

/-- `app:ch_mean_pairs:eq:mean-exact-self-change`: the polarization has the
complete Hermitian self tensor as its diagonal. -/
theorem mixedHermitianTensor_self (D : Matrix m n ℂ) :
    mixedHermitianTensor D D = hermitianTensor D := by
  rw [mixedHermitianTensor, symmetricBilinearTensor_self, symmetricBilinearTensor_self]
  ext i j
  simp [Matrix.mul_apply, hermitianTensor_apply, Finset.sum_add_distrib]

/-- `app:ch_mean_pairs:eq:mean-exact-self-change`: the real polarization
agrees with the symmetric real part of the Hermitian cross tensor. -/
theorem mixedHermitianTensor_eq_symmetricPart (D E : Matrix m n ℂ) :
    mixedHermitianTensor D E = matrixSymmetricPart ((Dᴴ * E).map Complex.re) := by
  ext i j
  simp only [mixedHermitianTensor, symmetricBilinearTensor_apply, Matrix.add_apply,
    Matrix.map_apply, matrixSymmetricPart, Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- `main:eq:full-recursion`: the matrix tensor as a real bilinear map. -/
def hermitianBilinear : Matrix m n ℂ →ₗ[ℝ] Matrix m n ℂ →ₗ[ℝ] Matrix n n ℝ :=
  LinearMap.mk₂ ℝ mixedHermitianTensor mixedHermitianTensor_add_left
    mixedHermitianTensor_smul_left
    (fun D E F ↦ by
      rw [mixedHermitianTensor_comm, mixedHermitianTensor_add_left,
        mixedHermitianTensor_comm E D, mixedHermitianTensor_comm F D])
    (fun c D E ↦ by
      rw [mixedHermitianTensor_comm, mixedHermitianTensor_smul_left,
        mixedHermitianTensor_comm E D])

variable {Ω ι : Type*} [Fintype ι]

/-- `main:eq:full-recursion`: the weighted real quadratic tensor before
applying the measurement contraction. Weights are used without inversion. -/
def weightedHermitianBilinear (μ : ι → ℝ) :
    (Ω → ι → Matrix m n ℂ) →ₗ[ℝ]
      (Ω → ι → Matrix m n ℂ) →ₗ[ℝ] (Ω → Matrix n n ℝ) :=
  LinearMap.mk₂ ℝ (fun D E x ↦ ∑ i, μ i • hermitianBilinear (D x i) (E x i))
    (fun D E F ↦ by
      ext x a b
      simp [map_add, smul_add, Finset.sum_add_distrib])
    (fun c D E ↦ by
      funext x
      simp [map_smul, smul_comm (μ _) c, Finset.smul_sum])
    (fun D E F ↦ by
      ext x a b
      simp [map_add, smul_add, Finset.sum_add_distrib])
    (fun c D E ↦ by
      funext x
      simp [map_smul, smul_comm (μ _) c, Finset.smul_sum])

/-- `main:eq:mean-equation`: the actual weighted Hermitian self tensor of
a finite family of complex derivative fields. -/
def weightedHermitianTensor (μ : ι → ℝ) (D : Ω → ι → Matrix m n ℂ) :
    Ω → Matrix n n ℝ := fun x ↦ ∑ i, μ i • hermitianTensor (D x i)

/-- `main:eq:full-recursion`: the quadratic map used by the recurrence is
exactly the complete weighted Hermitian tensor. -/
theorem weightedHermitianBilinear_self (μ : ι → ℝ) (D : Ω → ι → Matrix m n ℂ) :
    weightedHermitianBilinear μ D D = weightedHermitianTensor μ D := by
  funext x
  simp only [weightedHermitianBilinear, LinearMap.mk₂_apply, hermitianBilinear,
    mixedHermitianTensor_self, weightedHermitianTensor]

/-- `app:ch_mean_pairs:eq:mean-exact-self-change`: the exact change in the
weighted self tensor, with the original zero-atom derivative retained in the
linear cross term and the complete quadratic remainder. -/
theorem weightedHermitianTensor_add_sub (μ : ι → ℝ)
    (base change : Ω → ι → Matrix m n ℂ) :
    weightedHermitianTensor μ (base + change) - weightedHermitianTensor μ base =
      (2 : ℝ) • weightedHermitianBilinear μ base change +
        weightedHermitianTensor μ change := by
  funext x
  simp only [weightedHermitianTensor, Pi.sub_apply, Pi.add_apply,
    ← Finset.sum_sub_distrib, ← smul_sub, hermitianTensor_add_sub,
    weightedHermitianBilinear, LinearMap.mk₂_apply, hermitianBilinear,
    mixedHermitianTensor_eq_symmetricPart, Pi.smul_apply,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_comm (μ _) (2 : ℝ)]

end JanetCartan.CurrentMean
