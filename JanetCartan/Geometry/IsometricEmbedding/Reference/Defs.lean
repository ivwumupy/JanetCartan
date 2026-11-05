module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The flat cube reference

Definitions and statements from Section 2 and Appendix D of paper.tex.
All balls are centered at zero after choosing normalized local coordinates.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- Two nested physical balls inside one cell of the unit torus. -/
structure LocalDomain where
  /-- Radius of the closed ball on which the metric is corrected. -/
  coreRadius : ℝ
  /-- Radius of the larger construction chart. -/
  chartRadius : ℝ
  coreRadius_pos : 0 < coreRadius
  coreRadius_lt_chartRadius : coreRadius < chartRadius
  chartRadius_lt_half : chartRadius < 1 / 2

/-- The fixed closed core. -/
def LocalDomain.core (D : LocalDomain) (n : ℕ) : Set (Euclidean n) :=
  Metric.closedBall 0 D.coreRadius

/-- The open construction chart. -/
def LocalDomain.chart (D : LocalDomain) (n : ℕ) : Set (Euclidean n) :=
  Metric.ball 0 D.chartRadius

/-- A compact set on which coefficient seminorms are measured. -/
def LocalDomain.closureChart (D : LocalDomain) (n : ℕ) : Set (Euclidean n) :=
  Metric.closedBall 0 D.chartRadius

/-- The cube coefficient c_n = (n - 4)⁻². -/
def cubeCoefficient (n : ℕ) : ℝ := (((n : ℝ) - 4) ^ 2)⁻¹

/-- The frozen stresses Q_i = e_i e_iᵀ - c_n J. -/
def cubeStress (n : ℕ) (i : Fin n) : MetricTensor n :=
  fun j k ↦ (if j = i ∧ k = i then 1 else 0) - cubeCoefficient n

/-- The vector ℓ_ab = 1 - 2e_a - 2e_b. -/
def cubeVector {n : ℕ} (a b : Fin n) : Euclidean n :=
  WithLp.toLp 2 (fun i ↦ 1 - (if i = a then 2 else 0) - (if i = b then 2 else 0))

/-- Unordered distinct coordinate pairs, represented in increasing order. -/
abbrev CoordinatePair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The flat cube normal map on symmetric tensors. -/
def cubeNormalMap (n : ℕ) (H : MetricTensor n) :
    EuclideanSpace ℝ (CoordinatePair n) :=
  WithLp.toLp 2 fun p ↦
    ∑ i, ∑ j, H i j * cubeVector p.val.1 p.val.2 i * cubeVector p.val.1 p.val.2 j

/-- The real contraction pencil M₀(ξ). -/
def cubePencil {n : ℕ} (ξ : Euclidean n) : MetricTensor n :=
  fun i j ↦ (if i = j then ξ i else 0) - cubeCoefficient n * ∑ k, ξ k

/-- The characteristic polynomial p₀ = det M₀. -/
def cubeDeterminant {n : ℕ} (ξ : Euclidean n) : ℝ := (cubePencil ξ).det

/-- The frozen stresses are linearly independent; one diagonal entry minus an
off-diagonal entry recovers each coefficient in a linear combination. -/
theorem cubeStress_linearIndependent {n : ℕ} (hn : 5 ≤ n) :
    LinearIndependent ℝ (cubeStress n) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (Nat.le_trans (by decide) hn)
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨j, hji⟩ := exists_ne i
  have hentry (k : Fin n) :
      cubeStress n k i i - cubeStress n k i j = if k = i then 1 else 0 := by
    by_cases hki : k = i
    · subst k
      simp [cubeStress, hji]
    · simp [cubeStress, hki, Ne.symm hki]
  have hdiff := congrArg (fun H : MetricTensor n ↦ H i i - H i j) ha
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply,
    sub_self] at hdiff
  rw [← Finset.sum_sub_distrib] at hdiff
  simp_rw [← mul_sub, hentry, mul_ite, mul_one, mul_zero] at hdiff
  simpa using hdiff

private theorem det_diagonal_sub_const_of_ne_zero {n : ℕ} (d : Fin n → ℝ)
    (t : ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.of fun i j ↦ (if i = j then d i else 0) - t).det =
      (∏ i, d i) - t * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, d j := by
  have hfactor :
      (Matrix.of fun i j ↦ (if i = j then d i else 0) - t) =
        Matrix.diagonal d *
          (1 + Matrix.replicateCol Unit (fun i ↦ -t / d i) *
            Matrix.replicateRow Unit (fun _ ↦ (1 : ℝ))) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, mul_one,
      Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> field_simp [hd i] <;> ring
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul]
  rw [mul_add, mul_one, Finset.mul_sum]
  have hterm (i : Fin n) :
      (∏ j, d j) * (-t / d i) = -t * ∏ j ∈ Finset.univ.erase i, d j := by
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
    field_simp [hd i]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  ring

private theorem det_diagonal_sub_const {n : ℕ} (d : Fin n → ℝ) (t : ℝ) :
    (Matrix.of fun i j ↦ (if i = j then d i else 0) - t).det =
      (∏ i, d i) - t * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, d j := by
  have hdense : Dense {d : Fin n → ℝ | ∀ i, d i ≠ 0} := by
    simpa [Set.pi] using dense_pi (Set.univ : Set (Fin n))
      (fun _ _ ↦ dense_compl_singleton (0 : ℝ))
  have heq := Continuous.ext_on hdense
    (f := fun d : Fin n → ℝ ↦
      (Matrix.of fun i j ↦ (if i = j then d i else 0) - t).det)
    (g := fun d : Fin n → ℝ ↦
      (∏ i, d i) - t * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, d j)
    (by
      apply Continuous.matrix_det
      refine continuous_matrix fun i j ↦ ?_
      change Continuous (fun d : Fin n → ℝ ↦ (if i = j then d i else 0) - t)
      by_cases hij : i = j
      · simp only [hij, ite_true]
        fun_prop
      · simp only [hij, ite_false]
        exact continuous_const)
    (by fun_prop)
    (fun d hd ↦ det_diagonal_sub_const_of_ne_zero d t hd)
  exact congr_fun heq d

/-- Equation app:ch_seed:eq:seed-det, including covectors with zero coordinates. -/
theorem cubeDeterminant_eq {n : ℕ} (ξ : Euclidean n) :
    cubeDeterminant ξ =
      (∏ i, ξ i) - cubeCoefficient n * (∑ i, ξ i) *
        ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, ξ j := by
  exact det_diagonal_sub_const (fun i ↦ ξ i) (cubeCoefficient n * ∑ k, ξ k)

/-- The geometric properties of a fixed flat reference, before choosing the target dilation. -/
structure FlatReference (n : ℕ) where
  /-- The fixed physical domains. -/
  domain : LocalDomain
  /-- The reference immersion. -/
  map : Euclidean n → Euclidean (embeddingDimension n)
  contDiff : ContDiff ℝ ∞ map
  map_zero : map 0 = 0
  inducedMetric_eq_one : ∀ x, inducedMetric map x = 1
  fullNormalRank : HasFullNormalRankOn map (domain.chart n)
  stressSpace_zero :
    stressSpace map 0 = (Submodule.span ℝ (Set.range (cubeStress n)) : Set (MetricTensor n))

/-- Target dilation after normalizing g(0) = I. -/
def scaledMetric {n : ℕ} (g : MetricField n) (s : ℝ) : MetricField n :=
  fun x ↦ g (s • x)

end JanetCartan
