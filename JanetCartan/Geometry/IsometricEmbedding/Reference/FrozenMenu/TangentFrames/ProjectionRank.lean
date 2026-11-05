module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-!
# Projection ranks on the characteristic tangent space

The linear algebra in Step 3 of `app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

open CubeCarrier Module

/-- The characteristic tangent space at the carrier in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
def tangentSpace {n : ℕ} (ξ : Euclidean n) : Submodule ℝ (Euclidean n) :=
  (fderiv ℝ cubeDeterminant ξ).ker

/-- The bad-space projection restricted to the characteristic tangent space
in `app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
def tangentProjection {n : ℕ} (ξ : Euclidean n) (L : Submodule ℝ (Euclidean n)) :
    tangentSpace ξ →ₗ[ℝ] Lᗮ :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap.comp (tangentSpace ξ).subtype

/-- A normal witness is also a nonzero determinant-differential witness
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.differential_ne_zero_of_normal_pairing {n : ℕ}
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) {x : Euclidean n}
    (hx : (∑ a, x a * normal ξ a) ≠ 0) :
    fderiv ℝ cubeDeterminant ξ x ≠ 0 := by
  rw [determinant_differential h.coordinates_ne_zero h.characteristic]
  exact mul_ne_zero
    (determinant_normal_multiplier_ne_zero h.coordinates_ne_zero h.characteristic) hx

/-- Correcting a lift by a kernel vector makes it tangent without changing
its image (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem surjective_on_kernel_of_witness
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] ℝ) (g : V →ₗ[ℝ] W) (hg : Function.Surjective g)
    {x : V} (hx : g x = 0) (hfx : f x ≠ 0) :
    Function.Surjective (g.comp f.ker.subtype) := by
  intro y
  obtain ⟨z, rfl⟩ := hg y
  refine ⟨⟨z - (f z / f x) • x, ?_⟩, ?_⟩
  · simp [LinearMap.mem_ker, hfx]
  · simp [hx]

/-- The triple-zero witness gives surjectivity of the tangent projection
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.tangentProjection_triple_surjective {n : ℕ}
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) (i j l : Fin n) :
    Function.Surjective (tangentProjection ξ (cubeTripleZeroSpace i j l)) := by
  obtain ⟨x, hi, hj, hl, hx⟩ := h.triple_witness i j l
  unfold tangentProjection tangentSpace
  apply surjective_on_kernel_of_witness (x := x)
    (fderiv ℝ cubeDeterminant ξ).toLinearMap
    (cubeTripleZeroSpace i j l)ᗮ.orthogonalProjectionOnto.toLinearMap
  · intro y
    exact ⟨y, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  · apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using
      (show x ∈ cubeTripleZeroSpace i j l from ⟨hi, hj, hl⟩)
  · exact h.differential_ne_zero_of_normal_pairing hx

/-- The double-zero-sum witness gives surjectivity of the tangent projection
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.tangentProjection_pair_sum_surjective {n : ℕ}
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) (i j : Fin n) :
    Function.Surjective (tangentProjection ξ (cubeDoubleZeroSumSpace i j)) := by
  obtain ⟨x, hi, hj, hs, hx⟩ := h.pair_sum_witness i j
  unfold tangentProjection tangentSpace
  apply surjective_on_kernel_of_witness (x := x)
    (fderiv ℝ cubeDeterminant ξ).toLinearMap
    (cubeDoubleZeroSumSpace i j)ᗮ.orthogonalProjectionOnto.toLinearMap
  · intro y
    exact ⟨y, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  · apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using
      (show x ∈ cubeDoubleZeroSumSpace i j from ⟨hi, hj, hs⟩)
  · exact h.differential_ne_zero_of_normal_pairing hx

private def tripleCoordinates {n : ℕ} (i j l : Fin n) :
    Euclidean n →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x i, x j, x l]
  map_add' x y := by ext a; fin_cases a <;> rfl
  map_smul' t x := by ext a; fin_cases a <;> rfl

private theorem tripleCoordinates_surjective {n : ℕ} {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    Function.Surjective (tripleCoordinates i j l) := by
  intro u
  refine ⟨EuclideanSpace.single i (u 0) + EuclideanSpace.single j (u 1) +
    EuclideanSpace.single l (u 2), ?_⟩
  ext a
  fin_cases a <;> simp [tripleCoordinates, hij, hil, hjl, hij.symm, hil.symm, hjl.symm]

private def pairSumCoordinates {n : ℕ} (i j : Fin n) :
    Euclidean n →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x i, x j, ∑ a, x a]
  map_add' x y := by ext a; fin_cases a <;> simp [Finset.sum_add_distrib]
  map_smul' t x := by ext a; fin_cases a <;> simp [← Finset.mul_sum]

private theorem pairSumCoordinates_surjective {n : ℕ} (hn : 3 ≤ n) {i j : Fin n}
    (hij : i ≠ j) : Function.Surjective (pairSumCoordinates i j) := by
  classical
  have hc : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    simp [hij]; omega
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  intro u
  refine ⟨EuclideanSpace.single i (u 0) + EuclideanSpace.single j (u 1) +
    EuclideanSpace.single l (u 2 - u 0 - u 1), ?_⟩
  ext a
  fin_cases a <;>
    simp [pairSumCoordinates, hij, hij.symm, Ne.symm hl.1, Ne.symm hl.2,
      Finset.sum_add_distrib]

private theorem three_le_finrank_orthogonal_of_coordinates {n : ℕ}
    (L : Submodule ℝ (Euclidean n)) (C : Euclidean n →ₗ[ℝ] (Fin 3 → ℝ))
    (hC : Function.Surjective C) (hL : L ≤ C.ker) :
    3 ≤ finrank ℝ Lᗮ := by
  have hdim := C.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hC] at hdim
  simp at hdim
  have hle := Submodule.finrank_mono hL
  have horth := L.finrank_add_finrank_orthogonal
  simp only [finrank_euclideanSpace, Fintype.card_fin] at horth
  omega

/-- The codimension-three coordinate spaces have complements of dimension at
least three (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem three_le_finrank_tripleZeroSpace_orthogonal {n : ℕ} {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    3 ≤ finrank ℝ (cubeTripleZeroSpace i j l)ᗮ := by
  apply three_le_finrank_orthogonal_of_coordinates _ (tripleCoordinates i j l)
    (tripleCoordinates_surjective hij hil hjl)
  intro x hx
  rcases hx with ⟨hi, hj, hl⟩
  change ![x i, x j, x l] = 0
  ext a
  fin_cases a <;> simp [hi, hj, hl]

/-- The double-zero-sum spaces have complements of dimension at least three
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem three_le_finrank_doubleZeroSumSpace_orthogonal {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    3 ≤ finrank ℝ (cubeDoubleZeroSumSpace i j)ᗮ := by
  apply three_le_finrank_orthogonal_of_coordinates _ (pairSumCoordinates i j)
    (pairSumCoordinates_surjective hn hij)
  intro x hx
  rcases hx with ⟨hi, hj, hs⟩
  change ![x i, x j, ∑ a, x a] = 0
  ext a
  fin_cases a <;> simp [hi, hj, hs]

/-- A scalar differential has a kernel of dimension at least `n - 1`
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem tangentSpace_finrank_lower_bound {n : ℕ} (ξ : Euclidean n) :
    n ≤ finrank ℝ (tangentSpace ξ) + 1 := by
  have hdim := (fderiv ℝ cubeDeterminant ξ).toLinearMap.finrank_range_add_finrank_ker
  have hle := (fderiv ℝ cubeDeterminant ξ).toLinearMap.range.finrank_le
  simp only [finrank_euclideanSpace, Fintype.card_fin, finrank_self] at *
  change n ≤ finrank ℝ (fderiv ℝ cubeDeterminant ξ).ker + 1
  omega

/-- Restriction to the tangent space loses at most the dimension of the bad
space under orthogonal projection (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem tangentProjection_finrank_lower_bound {n : ℕ} (ξ : Euclidean n)
    (L : Submodule ℝ (Euclidean n)) :
    finrank ℝ (tangentSpace ξ) ≤ finrank ℝ (tangentProjection ξ L).range +
      finrank ℝ L := by
  let f := tangentProjection ξ L
  let g : f.ker →ₗ[ℝ] L := LinearMap.codRestrict L
    ((tangentSpace ξ).subtype.comp f.ker.subtype) (by
      intro x
      have hx : Lᗮ.orthogonalProjectionOnto (x : tangentSpace ξ) = 0 := x.property
      change (x.val : Euclidean n) ∈ L
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hx))
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : L ↦ (z : Euclidean n)) hxy
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  have hdim := f.finrank_range_add_finrank_ker
  change finrank ℝ (tangentSpace ξ) ≤ finrank ℝ f.range + finrank ℝ L
  omega

/-- Node lines have dimension at most one
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem cubeNodeLine_finrank_le_one {n : ℕ} (a b : Fin n) :
    finrank ℝ (cubeNodeLine a b) ≤ 1 := by
  classical
  change finrank ℝ (Submodule.span ℝ {cubeVector a b}) ≤ 1
  simpa using (finrank_span_le_card ({cubeVector a b} : Set (Euclidean n)))

/-- The node-line projections have rank at least `n - 2`, hence at least three
when `n ≥ 5` (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem tangentProjection_node_rank_lower_bound {n : ℕ} (ξ : Euclidean n)
    (a b : Fin n) : n - 2 ≤ finrank ℝ (tangentProjection ξ (cubeNodeLine a b)).range := by
  have := tangentSpace_finrank_lower_bound ξ
  have := tangentProjection_finrank_lower_bound ξ (cubeNodeLine a b)
  have := cubeNodeLine_finrank_le_one a b
  omega

/-- Every bad-space projection has rank at least three on the characteristic
tangent space of a seed (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.tangentProjection_rank_ge_three {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ)
    {L : Submodule ℝ (Euclidean n)} (hL : L ∈ cubeBadSubspaces n) :
    3 ≤ finrank ℝ (tangentProjection ξ L).range := by
  classical
  simp only [cubeBadSubspaces, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and] at hL
  rcases hL with (⟨⟨i, j, l⟩, ⟨hij, hil, hjl⟩, rfl⟩ |
    ⟨⟨i, j⟩, hij, rfl⟩) | ⟨⟨i, j⟩, _, rfl⟩
  · rw [LinearMap.range_eq_top.mpr (h.tangentProjection_triple_surjective i j l)]
    simpa using three_le_finrank_tripleZeroSpace_orthogonal hij hil hjl
  · rw [LinearMap.range_eq_top.mpr (h.tangentProjection_pair_sum_surjective i j)]
    simpa using three_le_finrank_doubleZeroSumSpace_orthogonal (by omega : 3 ≤ n) hij
  · exact (by omega : 3 ≤ n - 2).trans (tangentProjection_node_rank_lower_bound ξ i j)

end JanetCartan.FrozenMenu
