module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import JanetCartan.Geometry.IsometricEmbedding.Reference.DeterminantDeriv.Matrix

import Mathlib.Tactic.Ring

/-!
# The cube determinant differential and quadratic contraction

The differential identities in Proposition `app:ch_seed:prop:seed-strata` of
`paper.tex`. We prove Jacobi's formula for `cubePencil` and deduce `dp₀ = a q₀(v)`
from the explicit matrix identity `adj M₀ = a vvᵀ`.

To apply the latter result at a corank-one point, a separate linear algebra
argument must supply a nonzero kernel vector `v`, a scalar `a ≠ 0`, and that
adjugate factorization. To apply the zero-adjugate result at higher corank,
one must prove that corank at least two makes the adjugate zero. These inputs
are not asserted or assumed as consequences of corank in this module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan

/-- Definition app:ch_seed:defn:seed-cube: the cube pencil as a continuous linear
map, with the Frobenius norm on its matrix target. -/
def cubePencilContinuousLinearMap (n : ℕ) : Euclidean n →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap {
    toFun := cubePencil
    map_add' := by
      intro x y
      ext i j
      change cubePencil (x + y) i j = cubePencil x i j + cubePencil y i j
      simp only [cubePencil, PiLp.add_apply, Finset.sum_add_distrib, mul_add]
      split_ifs <;> ring
    map_smul' := by
      intro a x
      ext i j
      change cubePencil (a • x) i j = a * cubePencil x i j
      simp only [cubePencil, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      split_ifs <;> ring }

/-- Definition app:ch_seed:defn:seed-cube: the bundled pencil agrees with `M₀`. -/
@[simp] theorem cubePencilContinuousLinearMap_apply {n : ℕ} (ξ : Euclidean n) :
    cubePencilContinuousLinearMap n ξ = cubePencil ξ := rfl

/-- Proposition app:ch_seed:prop:seed-strata: the chain rule for `p₀ = det M₀`,
valid at singular as well as nonsingular pencils. -/
theorem hasFDerivAt_cubeDeterminant {n : ℕ} (ξ : Euclidean n) :
    HasFDerivAt cubeDeterminant
      ((fderiv ℝ Matrix.det (cubePencil ξ)).comp (cubePencilContinuousLinearMap n)) ξ :=
  (Matrix.differentiable_det (cubePencil ξ)).hasFDerivAt.comp ξ
    ((cubePencilContinuousLinearMap n).hasFDerivAt (x := ξ))

/-- Proposition app:ch_seed:prop:seed-strata: the determinant differential is
`h ↦ tr (adj(M₀(ξ)) M₀(h))`. -/
theorem fderiv_cubeDeterminant_apply {n : ℕ} (ξ h : Euclidean n) :
    fderiv ℝ cubeDeterminant ξ h =
      ((cubePencil ξ).adjugate * cubePencil h).trace := by
  rw [(hasFDerivAt_cubeDeterminant ξ).fderiv, ContinuousLinearMap.comp_apply,
    cubePencilContinuousLinearMap_apply, Matrix.fderiv_det_apply]

/-- Proposition app:ch_seed:prop:seed-strata: the coordinate adjugate formula
for the determinant differential. -/
theorem fderiv_cubeDeterminant_apply_sum {n : ℕ} (ξ h : Euclidean n) :
    fderiv ℝ cubeDeterminant ξ h =
      ∑ i, ∑ j, (cubePencil ξ).adjugate j i * cubePencil h i j := by
  rw [fderiv_cubeDeterminant_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_comm

/-- Definition app:ch_seed:defn:seed-cube: the quadratic contraction
`q₀(v) = (vᵀ Qᵢ⁰ v)ᵢ`. -/
def cubeQuadraticContraction {n : ℕ} (v : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 fun i ↦ ∑ j, ∑ k, v j * cubeStress n i j k * v k

/-- Definition app:ch_seed:defn:seed-cube: the coordinate formula for `q₀`. -/
theorem cubeQuadraticContraction_apply {n : ℕ} (v : Euclidean n) (i : Fin n) :
    cubeQuadraticContraction v i = v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 := by
  change (∑ j, ∑ k, v j * ((if j = i ∧ k = i then 1 else 0) - cubeCoefficient n) * v k) = _
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ite_and]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Definition app:ch_seed:defn:seed-cube: the identity `M₀(v)v = q₀(v)`. -/
theorem cubePencil_mulVec_self {n : ℕ} (v : Euclidean n) (i : Fin n) :
    (cubePencil v *ᵥ (fun j ↦ v j)) i = cubeQuadraticContraction v i := by
  rw [cubeQuadraticContraction_apply]
  simp only [Matrix.mulVec, dotProduct, cubePencil, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  ring

/-- Definition app:ch_seed:defn:seed-cube: the pencil is the linear combination
of the frozen stresses. -/
theorem cubePencil_eq_sum_smul_cubeStress {n : ℕ} (h : Euclidean n) :
    cubePencil h = ∑ k, h k • cubeStress n k := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, cubeStress,
    mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ← Finset.sum_mul]
  by_cases hij : i = j
  · subst j
    simp [cubePencil, mul_comm]
  · simp [cubePencil, hij, show ∀ k, ¬ (i = k ∧ j = k) from
      fun k hk ↦ hij (hk.1.trans hk.2.symm), mul_comm]

/-- Proposition app:ch_seed:prop:seed-strata: an actual adjugate factorization
gives the contraction `dp₀(ξ)h = a ∑ᵢ q₀(v)ᵢ hᵢ`. No corank hypothesis is
substituted for the factorization. -/
theorem fderiv_cubeDeterminant_apply_of_adjugate_eq {n : ℕ} (x v h : Euclidean n) (a : ℝ)
    (hf : (cubePencil x).adjugate = fun i j ↦ a * v i * v j) :
    fderiv ℝ cubeDeterminant x h = a * ∑ k, cubeQuadraticContraction v k * h k := by
  rw [fderiv_cubeDeterminant_apply_sum, hf, cubePencil_eq_sum_smul_cubeStress]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ j, ∑ i, a * v j * v i * (h k * cubeStress n k i j)) =
    a * ((∑ i, ∑ j, v i * cubeStress n k i j * v j) * h k)
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Proposition app:ch_seed:prop:seed-strata: `dp₀ = a q₀(v)` as a covector,
using the Euclidean inner product to identify vectors and covectors. -/
theorem fderiv_cubeDeterminant_of_adjugate_eq {n : ℕ} (x v : Euclidean n) (a : ℝ)
    (hf : (cubePencil x).adjugate = fun i j ↦ a * v i * v j) :
    fderiv ℝ cubeDeterminant x = a • innerSL ℝ (cubeQuadraticContraction v) := by
  ext h
  rw [fderiv_cubeDeterminant_apply_of_adjugate_eq x v h a hf]
  simp [PiLp.inner_apply, mul_comm]

/-- Proposition app:ch_seed:prop:seed-strata: the coordinate version of
`dp₀ = a q₀(v)` under the adjugate factorization. -/
theorem partialDeriv_cubeDeterminant_of_adjugate_eq {n : ℕ} (x v : Euclidean n) (a : ℝ)
    (hf : (cubePencil x).adjugate = fun i j ↦ a * v i * v j) (i : Fin n) :
    partialDeriv cubeDeterminant x i = a * cubeQuadraticContraction v i := by
  rw [partialDeriv, fderiv_cubeDeterminant_of_adjugate_eq x v a hf]
  simp [EuclideanSpace.inner_single_right]

/-- Proposition app:ch_seed:prop:seed-strata: a nonzero factor in the adjugate
reduces vanishing of the determinant differential to the common quadratic zeros. -/
theorem fderiv_cubeDeterminant_eq_zero_iff_of_adjugate_eq {n : ℕ}
    (x v : Euclidean n) (a : ℝ) (ha : a ≠ 0)
    (hf : (cubePencil x).adjugate = fun i j ↦ a * v i * v j) :
    fderiv ℝ cubeDeterminant x = 0 ↔ cubeQuadraticContraction v = 0 := by
  constructor
  · intro hd
    ext i
    have hi := partialDeriv_cubeDeterminant_of_adjugate_eq x v a hf i
    rw [partialDeriv, hd] at hi
    simpa using (mul_eq_zero.mp hi.symm).resolve_left ha
  · intro hq
    rw [fderiv_cubeDeterminant_of_adjugate_eq x v a hf, hq]
    simp

/-- Proposition app:ch_seed:prop:seed-strata: a zero adjugate forces a zero
determinant differential. -/
theorem fderiv_cubeDeterminant_eq_zero_of_adjugate_eq_zero {n : ℕ} (x : Euclidean n)
    (h : (cubePencil x).adjugate = 0) : fderiv ℝ cubeDeterminant x = 0 := by
  ext v
  rw [fderiv_cubeDeterminant_apply, h]
  simp

end JanetCartan
