module

public import JanetCartan.Geometry.IsometricEmbedding.Normal
public import JanetCartan.Analysis.ContDiff.Norm
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Strata
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Dilation

/-!
# Completed reference statements

The original manuscript statements, assembled from their constructive leaf proofs.
Shared definitions live in `Reference/Defs.lean` to keep the import graph acyclic.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- Proposition app:ch_seed:prop:seed-gram: full rank and the precise stress kernel. -/
theorem cube_normal_rank_and_kernel {n : ℕ} (hn : 5 ≤ n) :
    LinearIndependent ℝ (cubeStress n) ∧
    (∀ v : EuclideanSpace ℝ (CoordinatePair n),
      ∃ H : MetricTensor n, H.IsSymm ∧ cubeNormalMap n H = v) ∧
    ∀ H : MetricTensor n, H.IsSymm →
      (cubeNormalMap n H = 0 ↔ H ∈ Submodule.span ℝ (Set.range (cubeStress n))) := by
  exact cubeNormalMap_rank_and_kernel hn

/-- Proposition app:ch_seed:prop:seed-strata: the complete nonzero multiple set. -/
theorem cubeDeterminant_eq_zero_and_fderiv_eq_zero_iff {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    (cubeDeterminant ξ = 0 ∧ fderiv ℝ cubeDeterminant ξ = 0) ↔
      (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0) ∨
      (∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0) ∨
      (∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, ξ = t • cubeVector a b) := by
  exact cubeDeterminant_multiple_iff_strata hn hξ

/-- Proposition app:ch_seed:prop:seed-analytic and its fixed normalization:
an analytic flat reference with the cube stress space exists. -/
theorem exists_flatReference {n : ℕ} (hn : 5 ≤ n) :
    ∃ G : FlatReference n, AnalyticOnNhd ℝ G.map Set.univ := by
  exact exists_analytic_flatReference hn

/-- Proposition main:prop:seed: the reference is independent of the target dilation. -/
theorem scaledMetric_sub_inducedMetric_bound {n : ℕ} (G : FlatReference n)
    {g : MetricField n} (hg : ContDiff ℝ ∞ g) (hg₀ : g 0 = 1) :
    ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      cNorm (G.domain.closureChart n) r (scaledMetric g s - inducedMetric G.map) ≤ C * s := by
  exact scaledMetric_sub_inducedMetric_bound_of_contDiff G hg hg₀

end JanetCartan
