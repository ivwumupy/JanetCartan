module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Independence of the cube rank-one forms

The independence argument in Proposition `app:ch_seed:prop:seed-gram` of `paper.tex`.
The forms associated to `e_a + e_b` have distinct off-diagonal entries. Conjugating
by the invertible matrix `-2(I - J/4)` transfers their independence to the cube
vectors. The number of forms is the normal dimension `n * (n - 1) / 2`.
-/

@[expose] public noncomputable section

open Matrix

namespace JanetCartan

/-- Proposition app:ch_seed:prop:seed-gram: the increasing coordinate pairs number `n.choose 2`. -/
theorem coordinatePair_card_choose (n : ℕ) :
    Fintype.card (CoordinatePair n) = n.choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- Proposition app:ch_seed:prop:seed-gram: the number of cube forms is the normal dimension. -/
theorem coordinatePair_card (n : ℕ) :
    Fintype.card (CoordinatePair n) = normalDimension n := by
  rw [coordinatePair_card_choose, Nat.choose_two_right, normalDimension]

/-- The vector `e_a + e_b` used in Proposition app:ch_seed:prop:seed-gram. -/
def pairSupportVector {n : ℕ} (p : CoordinatePair n) : Fin n → ℝ :=
  Pi.single p.val.1 1 + Pi.single p.val.2 1

/-- Proposition app:ch_seed:prop:seed-gram: an off-diagonal entry singles out its coordinate pair. -/
theorem pairSupportVector_rankOne_entry {n : ℕ} (p q : CoordinatePair n) :
    vecMulVec (pairSupportVector p) (pairSupportVector p) q.val.1 q.val.2 =
      if p = q then 1 else 0 := by
  have hp := p.property
  have hq := q.property
  by_cases h : p = q
  · subst p
    simp [vecMulVec, pairSupportVector, Pi.single_apply, hq.ne, hq.ne.symm]
  · have hval : p.val ≠ q.val := fun he ↦ h (Subtype.ext he)
    have hpq : ¬ (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) :=
      fun he ↦ hval (Prod.ext he.1 he.2)
    simp only [vecMulVec_apply, pairSupportVector, Pi.add_apply, Pi.single_apply,
      ite_eq_right h]
    split_ifs <;> simp_all
    exact lt_asymm hp hq

/-- Proposition app:ch_seed:prop:seed-gram: the forms `(e_a + e_b)(e_a + e_b)ᵀ` are independent. -/
theorem pairSupportVector_rankOne_linearIndependent (n : ℕ) :
    LinearIndependent ℝ (fun p : CoordinatePair n ↦
      vecMulVec (pairSupportVector p) (pairSupportVector p)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have he := congrArg (fun H : MetricTensor n ↦ H q.val.1 q.val.2) hc
  simpa [Matrix.sum_apply, Matrix.smul_apply, pairSupportVector_rankOne_entry] using he

/-- The change of vectors `-2(I - J/4)` in Proposition app:ch_seed:prop:seed-gram. -/
def cubeChangeMatrix (n : ℕ) : MetricTensor n :=
  (-2 : ℝ) • (1 + replicateCol Unit (fun _ ↦ (-1 / 4 : ℝ)) *
    replicateRow Unit (fun _ ↦ (1 : ℝ)))

/-- Proposition app:ch_seed:prop:seed-gram: the entries of the change of vectors. -/
theorem cubeChangeMatrix_apply {n : ℕ} (i j : Fin n) :
    cubeChangeMatrix n i j = -2 * (if i = j then 1 else 0) + 1 / 2 := by
  by_cases h : i = j <;> norm_num [cubeChangeMatrix, Matrix.mul_apply, h]

/-- Proposition app:ch_seed:prop:seed-gram: the determinant of `-2(I - J/4)`,
computed using the rank-one determinant lemma. -/
theorem cubeChangeMatrix_det (n : ℕ) :
    (cubeChangeMatrix n).det = (-2 : ℝ) ^ n * (1 - (n : ℝ) / 4) := by
  rw [cubeChangeMatrix, Matrix.det_smul,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring

/-- Proposition app:ch_seed:prop:seed-gram: the change of vectors is nonsingular for `n ≥ 5`. -/
theorem cubeChangeMatrix_det_ne_zero {n : ℕ} (hn : 5 ≤ n) :
    (cubeChangeMatrix n).det ≠ 0 := by
  rw [cubeChangeMatrix_det]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Proposition app:ch_seed:prop:seed-gram: `ℓ_ab = -2(I - J/4)(e_a + e_b)`. -/
theorem cubeChangeMatrix_mulVec_pairSupportVector {n : ℕ} (p : CoordinatePair n) :
    cubeChangeMatrix n *ᵥ pairSupportVector p =
      (fun i ↦ cubeVector p.val.1 p.val.2 i) := by
  ext i
  simp only [pairSupportVector, Matrix.mulVec_add, Matrix.mulVec_single_one,
    Pi.add_apply, Matrix.col_apply, cubeChangeMatrix_apply, cubeVector]
  change (-2 * (if i = p.val.1 then 1 else 0) + 1 / 2) +
    (-2 * (if i = p.val.2 then 1 else 0) + 1 / 2) =
    1 - (if i = p.val.1 then 2 else 0) - (if i = p.val.2 then 2 else 0)
  split_ifs <;> norm_num

/-- Proposition app:ch_seed:prop:seed-gram: the cube forms are the congruence transforms
of the forms associated to `e_a + e_b`. -/
theorem cubeVector_rankOne_eq_conjugate {n : ℕ} (p : CoordinatePair n) :
    vecMulVec (fun i ↦ cubeVector p.val.1 p.val.2 i)
        (fun i ↦ cubeVector p.val.1 p.val.2 i) =
      cubeChangeMatrix n * vecMulVec (pairSupportVector p) (pairSupportVector p) *
        (cubeChangeMatrix n)ᵀ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    cubeChangeMatrix_mulVec_pairSupportVector]

/-- Proposition app:ch_seed:prop:seed-gram: the `n.choose 2` forms `ℓ_ab ℓ_abᵀ`
are linearly independent for `n ≥ 5`. -/
theorem cubeVector_rankOne_linearIndependent {n : ℕ} (hn : 5 ≤ n) :
    LinearIndependent ℝ (fun p : CoordinatePair n ↦
      vecMulVec (fun i ↦ cubeVector p.val.1 p.val.2 i)
        (fun i ↦ cubeVector p.val.1 p.val.2 i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply (Fintype.linearIndependent_iff.mp (pairSupportVector_rankOne_linearIndependent n)) c
  have hdet : IsUnit (cubeChangeMatrix n).det :=
    isUnit_iff_ne_zero.mpr (cubeChangeMatrix_det_ne_zero hn)
  have hdetT : IsUnit ((cubeChangeMatrix n)ᵀ).det := by
    simpa using hdet
  have he : cubeChangeMatrix n *
      (∑ p, c p • vecMulVec (pairSupportVector p) (pairSupportVector p)) *
        (cubeChangeMatrix n)ᵀ = 0 := by
    simpa only [cubeVector_rankOne_eq_conjugate, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul] using hc
  have he' := congrArg (fun H ↦ (cubeChangeMatrix n)⁻¹ * H *
    ((cubeChangeMatrix n)ᵀ)⁻¹) he
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
    Matrix.mul_nonsing_inv_cancel_right _ _ hdetT, Matrix.mul_zero, Matrix.zero_mul] using he'

end JanetCartan
