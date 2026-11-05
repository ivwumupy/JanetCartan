module

public import JanetCartan.Geometry.IsometricEmbedding.Basic

import Mathlib.Analysis.Matrix.Order

/-!
# Linear coordinate changes

The normalization of a positive definite metric used in `main:prop:seed`.
The matrix norm remains the Frobenius norm.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan

/-- Section 2, `main:prop:seed`: the Euclidean linear map represented by a matrix. -/
def coordinateMap {n : ℕ} (A : MetricTensor n) : Euclidean n →L[ℝ] Euclidean n :=
  A.toEuclideanLin.toContinuousLinearMap

/-- Section 2, `main:prop:seed`: the entries of the linear coordinate map. -/
@[simp] theorem coordinateMap_apply {n : ℕ} (A : MetricTensor n) (x : Euclidean n)
    (i : Fin n) : coordinateMap A x i = ∑ j, A i j * x j := rfl

/-- Section 2, `main:prop:seed`: the identity matrix preserves coordinates. -/
@[simp] theorem coordinateMap_one {n : ℕ} (x : Euclidean n) :
    coordinateMap (1 : MetricTensor n) x = x := by
  ext i
  simp [coordinateMap_apply, Matrix.one_apply]

/-- Section 2, `main:prop:seed`: matrix multiplication composes coordinate maps. -/
theorem coordinateMap_mul {n : ℕ} (A B : MetricTensor n) (x : Euclidean n) :
    coordinateMap (A * B) x = coordinateMap A (coordinateMap B x) := by
  exact congrArg (fun L : Euclidean n →ₗ[ℝ] Euclidean n ↦ L x)
    (Matrix.toLpLin_mul 2 2 2 A B)

/-- Section 2, `main:prop:seed`: a nonsingular matrix gives an invertible continuous
linear change of Euclidean coordinates, with inverse represented by `A⁻¹`. -/
def coordinateEquiv {n : ℕ} (A : MetricTensor n) (hA : IsUnit A) :
    Euclidean n ≃L[ℝ] Euclidean n where
  toLinearMap := A.toEuclideanLin
  invFun := coordinateMap A⁻¹
  left_inv x := by
    change coordinateMap A⁻¹ (coordinateMap A x) = x
    rw [← coordinateMap_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    exact coordinateMap_one x
  right_inv x := by
    change coordinateMap A (coordinateMap A⁻¹ x) = x
    rw [← coordinateMap_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    exact coordinateMap_one x
  continuous_toFun := (coordinateMap A).continuous
  continuous_invFun := (coordinateMap A⁻¹).continuous

/-- Section 2, `main:prop:seed`: the forward coordinate equivalence. -/
@[simp] theorem coordinateEquiv_apply {n : ℕ} (A : MetricTensor n) (hA : IsUnit A)
    (x : Euclidean n) : coordinateEquiv A hA x = coordinateMap A x := rfl

/-- Section 2, `main:prop:seed`: its inverse is the inverse matrix. -/
@[simp] theorem coordinateEquiv_symm_apply {n : ℕ} (A : MetricTensor n) (hA : IsUnit A)
    (x : Euclidean n) : (coordinateEquiv A hA).symm x = coordinateMap A⁻¹ x := rfl

/-- Section 2, `main:prop:seed`: the tensor pullback under `x = A y`. -/
def coordinatePullback {n : ℕ} (g : MetricField n) (A : MetricTensor n) : MetricField n :=
  fun x ↦ A.transpose * g (coordinateMap A x) * A

/-- Section 2, `main:prop:seed`: identity pullback preserves the metric. -/
@[simp] theorem coordinatePullback_one {n : ℕ} (g : MetricField n) :
    coordinatePullback g 1 = g := by
  funext x
  simp [coordinatePullback]

/-- Section 2, `main:prop:seed`: successive coordinate changes compose. -/
theorem coordinatePullback_comp {n : ℕ} (g : MetricField n) (A B : MetricTensor n) :
    coordinatePullback (coordinatePullback g A) B = coordinatePullback g (A * B) := by
  funext x
  simp [coordinatePullback, coordinateMap_mul, Matrix.transpose_mul, mul_assoc]

/-- Section 2, `main:prop:seed`: undoing an invertible coordinate change. -/
theorem coordinatePullback_inv {n : ℕ} (g : MetricField n) (A : MetricTensor n)
    (hA : IsUnit A) : coordinatePullback (coordinatePullback g A) A⁻¹ = g := by
  rw [coordinatePullback_comp, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det A).mp hA), coordinatePullback_one]

/-- Section 2, `main:prop:seed`: local smoothness is preserved by linear pullback. -/
theorem contDiffOn_coordinatePullback {n : ℕ} {g : MetricField n}
    {U : Set (Euclidean n)} (hg : ContDiffOn ℝ ∞ g U) (A : MetricTensor n) :
    ContDiffOn ℝ ∞ (coordinatePullback g A) (coordinateMap A ⁻¹' U) := by
  exact (contDiffOn_const.mul
    (hg.comp (coordinateMap A).contDiff.contDiffOn (fun _ hx ↦ hx))).mul contDiffOn_const

/-- Section 2, `main:prop:seed`: invertible pullback preserves positive definiteness. -/
theorem posDef_coordinatePullback {n : ℕ} {g : MetricField n} (A : MetricTensor n)
    (hA : IsUnit A) {x : Euclidean n} (hg : (g (coordinateMap A x)).PosDef) :
    (coordinatePullback g A x).PosDef := by
  simpa only [coordinatePullback, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hg.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hA)

/-- Section 2, `main:prop:seed`: a smooth Riemannian metric remains one on the
inverse-image domain. -/
theorem isRiemannianMetricOn_coordinatePullback {n : ℕ} {g : MetricField n}
    {U : Set (Euclidean n)} (hg : IsRiemannianMetricOn g U) (A : MetricTensor n)
    (hA : IsUnit A) :
    IsRiemannianMetricOn (coordinatePullback g A) (coordinateMap A ⁻¹' U) :=
  ⟨contDiffOn_coordinatePullback hg.1 A,
    fun _ hx ↦ posDef_coordinatePullback A hA (hg.2 _ hx)⟩

open scoped MatrixOrder in
/-- Section 2, `main:prop:seed`: the inverse positive square root normalizes a
positive definite matrix, including the zero-dimensional case. -/
theorem exists_normalizing_matrix {n : ℕ} {G : MetricTensor n} (hG : G.PosDef) :
    ∃ A : MetricTensor n, IsUnit A ∧ A.transpose * G * A = 1 := by
  let S := CFC.sqrt G
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).mpr hG.isUnit
  have hsym : S.transpose = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)).isHermitian.eq
  have hsq : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  refine ⟨S⁻¹, Matrix.isUnit_nonsing_inv_iff.mpr hS, ?_⟩
  rw [Matrix.transpose_nonsing_inv, hsym, ← hsq, ← mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det S).mp hS), one_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)]

/-- Section 2, `main:prop:seed`: choose coordinates with `g(0) = I`, preserving
the open neighborhood, smoothness and positive definiteness. -/
theorem exists_normalized_coordinates {n : ℕ} {g : MetricField n}
    {U : Set (Euclidean n)} (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hg : IsRiemannianMetricOn g U) :
    ∃ A : MetricTensor n, IsUnit A ∧
      IsOpen (coordinateMap A ⁻¹' U) ∧ (0 : Euclidean n) ∈ coordinateMap A ⁻¹' U ∧
      IsRiemannianMetricOn (coordinatePullback g A) (coordinateMap A ⁻¹' U) ∧
      coordinatePullback g A 0 = 1 := by
  obtain ⟨A, hA, hnorm⟩ := exists_normalizing_matrix (hg.2 0 h0)
  exact ⟨A, hA, hU.preimage (coordinateMap A).continuous, by simpa using h0,
    isRiemannianMetricOn_coordinatePullback hg A hA, by simpa [coordinatePullback] using hnorm⟩

/-- Section 2, `main:prop:seed`: linear coordinate changes preserve open
neighborhoods of the base point. -/
theorem coordinate_preimage_neighborhood {n : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (A : MetricTensor n) :
    IsOpen (coordinateMap A ⁻¹' U) ∧ (0 : Euclidean n) ∈ coordinateMap A ⁻¹' U :=
  ⟨hU.preimage (coordinateMap A).continuous, by simpa using h0⟩

end JanetCartan
