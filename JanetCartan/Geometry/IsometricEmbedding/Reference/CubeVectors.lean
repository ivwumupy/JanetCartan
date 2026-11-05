module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cube vectors and stress annihilation

The coordinate identities and stress annihilation used in the proof of
Proposition `app:ch_seed:prop:seed-gram` of `paper.tex`. Rank-one forms are expressed
using `Matrix.vecMulVec`, and their contraction uses the existing Frobenius pairing.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

variable {n : ℕ}

/-- Definition `app:ch_seed:defn:seed-cube`: the coordinates of ℓ_ab. -/
theorem cubeVector_apply (a b i : Fin n) :
    cubeVector a b i = 1 - (if i = a then 2 else 0) - (if i = b then 2 else 0) := rfl

/-- Proposition `app:ch_seed:prop:seed-gram`: the coordinate at the first index is −1. -/
theorem cubeVector_apply_left {a b : Fin n} (hab : a ≠ b) :
    cubeVector a b a = -1 := by
  norm_num [cubeVector_apply, hab]

/-- Proposition `app:ch_seed:prop:seed-gram`: the coordinate at the second index is −1. -/
theorem cubeVector_apply_right {a b : Fin n} (hab : a ≠ b) :
    cubeVector a b b = -1 := by
  norm_num [cubeVector_apply, hab.symm]

/-- Proposition `app:ch_seed:prop:seed-gram`: all other coordinates are 1. -/
theorem cubeVector_apply_of_ne {a b i : Fin n} (hia : i ≠ a) (hib : i ≠ b) :
    cubeVector a b i = 1 := by
  simp [cubeVector_apply, hia, hib]

/-- Proposition `app:ch_seed:prop:seed-gram`: every coordinate of ℓ_ab has square 1. -/
theorem cubeVector_apply_sq {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    (cubeVector a b i) ^ 2 = 1 := by
  by_cases hia : i = a
  · subst i
    rw [cubeVector_apply_left hab]
    norm_num
  by_cases hib : i = b
  · subst i
    rw [cubeVector_apply_right hab]
    norm_num
  rw [cubeVector_apply_of_ne hia hib]
  norm_num

/-- Proposition `app:ch_seed:prop:seed-gram`: the coordinate sum S_ℓ is n − 4.
This identity also holds when the two indices coincide. -/
theorem sum_cubeVector (a b : Fin n) :
    ∑ i, cubeVector a b i = (n : ℝ) - 4 := by
  simp only [cubeVector_apply, Finset.sum_sub_distrib]
  simp
  ring

/-- Proposition `app:ch_seed:prop:seed-gram`: the squared Euclidean norm of ℓ_ab is n. -/
theorem cubeVector_norm_sq {a b : Fin n} (hab : a ≠ b) :
    ‖cubeVector a b‖ ^ 2 = (n : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [cubeVector_apply_sq hab]

/-- Definition `app:ch_seed:defn:seed-cube`: contracting Q_i with vvᵀ gives
v_i² − c_n S_v². -/
theorem tensorPairing_cubeStress_vecMulVec (i : Fin n) (v : Fin n → ℝ) :
    tensorPairing (cubeStress n i) (Matrix.vecMulVec v v) =
      (v i) ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 := by
  simp only [tensorPairing, cubeStress, Matrix.vecMulVec_apply, sub_mul,
    Finset.sum_sub_distrib]
  have hdiag : (∑ j, ∑ k, (if j = i ∧ k = i then (1 : ℝ) else 0) * (v j * v k)) =
      (v i) ^ 2 := by
    simp only [ite_and, ite_mul, one_mul, zero_mul]
    simp [pow_two]
  rw [hdiag]
  congr 1
  simp_rw [← mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

/-- Definition `app:ch_seed:defn:seed-cube`: c_n (n − 4)² = 1 in the source range n ≥ 5. -/
theorem cubeCoefficient_mul_sub_four_sq (hn : 5 ≤ n) :
    cubeCoefficient n * ((n : ℝ) - 4) ^ 2 = 1 := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) - 4 ≠ 0 := by linarith
  exact inv_mul_cancel₀ (pow_ne_zero 2 hd)

/-- Proposition `app:ch_seed:prop:seed-gram`: every stress Q_i annihilates ℓ_ab ℓ_abᵀ. -/
theorem tensorPairing_cubeStress_cubeVector (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    tensorPairing (cubeStress n i)
      (Matrix.vecMulVec (cubeVector a b) (cubeVector a b)) = 0 := by
  rw [tensorPairing_cubeStress_vecMulVec, cubeVector_apply_sq hab,
    sum_cubeVector, cubeCoefficient_mul_sub_four_sq hn, sub_self]

/-- Proposition `app:ch_seed:prop:seed-gram`: each rank-one form ℓ_ab ℓ_abᵀ
annihilates every cube stress under the Frobenius pairing. -/
theorem tensorPairing_cubeVector_cubeStress (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    tensorPairing (Matrix.vecMulVec (cubeVector a b) (cubeVector a b))
      (cubeStress n i) = 0 := by
  simpa only [tensorPairing, mul_comm] using tensorPairing_cubeStress_cubeVector hn hab i

/-- Proposition `app:ch_seed:prop:seed-gram`: every cube stress lies in the kernel
of the cube normal map. -/
theorem cubeNormalMap_cubeStress (hn : 5 ≤ n) (i : Fin n) :
    cubeNormalMap n (cubeStress n i) = 0 := by
  ext p
  change (∑ j, ∑ k, cubeStress n i j k * cubeVector p.val.1 p.val.2 j *
    cubeVector p.val.1 p.val.2 k) = 0
  simpa only [tensorPairing, Matrix.vecMulVec_apply, mul_assoc] using
    tensorPairing_cubeStress_cubeVector hn (ne_of_lt p.property) i

end JanetCartan
