module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Kernel and corank of the cube pencil

The kernel classification and the codimension-three strata in the proof of
Proposition `app:ch_seed:prop:seed-strata` of `paper.tex`.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- The kernel of the coordinate matrix in `app:ch_seed:defn:seed-cube`. -/
def cubePencilKernel {n : ℕ} (ξ : Euclidean n) : Submodule ℝ (Fin n → ℝ) :=
  (cubePencil ξ).mulVecLin.ker

/-- The zero coordinates in `app:ch_seed:prop:seed-strata`. -/
def cubeZeroCoordinates {n : ℕ} (ξ : Euclidean n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ξ i = 0

@[simp] theorem mem_cubeZeroCoordinates {n : ℕ} (ξ : Euclidean n) (i : Fin n) :
    i ∈ cubeZeroCoordinates ξ ↔ ξ i = 0 := by
  simp [cubeZeroCoordinates]

/-- The coefficient in `app:ch_seed:defn:seed-cube` is nonzero in the source dimension. -/
theorem cubeCoefficient_ne_zero_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    cubeCoefficient n ≠ 0 := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  exact inv_ne_zero (pow_ne_zero _ (by linarith))

/-- Coordinate form of the kernel equation in `app:ch_seed:prop:seed-strata`. -/
theorem mem_cubePencilKernel_iff {n : ℕ} (ξ : Euclidean n) (v : Fin n → ℝ) :
    v ∈ cubePencilKernel ξ ↔
      ∀ i, ξ i * v i = cubeCoefficient n * (∑ j, ξ j) * ∑ j, v j := by
  change (cubePencil ξ).mulVec v = 0 ↔ _
  rw [funext_iff]
  simp only [Matrix.mulVec, dotProduct, cubePencil, Pi.zero_apply, sub_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_eq_zero]

/-- When `S_ξ = 0`, the kernel is exactly the vectors supported on the zero coordinates
(`app:ch_seed:prop:seed-strata`). -/
theorem mem_cubePencilKernel_iff_of_sum_eq_zero {n : ℕ} {ξ : Euclidean n}
    (hS : ∑ i, ξ i = 0) (v : Fin n → ℝ) :
    v ∈ cubePencilKernel ξ ↔ ∀ i, ξ i ≠ 0 → v i = 0 := by
  rw [mem_cubePencilKernel_iff]
  simp only [hS, mul_zero]
  exact forall_congr' fun i ↦ by simp [mul_eq_zero, or_iff_not_imp_left]

/-- With nonzero `S_ξ` and a zero coordinate, the kernel consists of zero-sum vectors
supported on the zero coordinates (`app:ch_seed:prop:seed-strata`). -/
theorem mem_cubePencilKernel_iff_of_sum_ne_zero {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hS : ∑ i, ξ i ≠ 0) (hz : ∃ i, ξ i = 0)
    (v : Fin n → ℝ) :
    v ∈ cubePencilKernel ξ ↔ (∀ i, ξ i ≠ 0 → v i = 0) ∧ ∑ i, v i = 0 := by
  rw [mem_cubePencilKernel_iff]
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := hz
    have hvS : ∑ j, v j = 0 := by
      have := hv i
      rw [hi, zero_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_left
        (mul_ne_zero (cubeCoefficient_ne_zero_of_five_le hn) hS)
    refine ⟨fun i hi ↦ ?_, hvS⟩
    have := hv i
    rw [hvS, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hi
  · rintro ⟨hv, hvS⟩ i
    rw [hvS, mul_zero]
    by_cases hi : ξ i = 0
    · simp [hi]
    · simp [hv i hi]

/-- With no zero coordinates, each kernel vector is determined by its coordinate sum
(`app:ch_seed:prop:seed-strata`). -/
theorem mem_cubePencilKernel_iff_of_coordinates_ne_zero {n : ℕ} {ξ : Euclidean n}
    (hz : ∀ i, ξ i ≠ 0) (v : Fin n → ℝ) :
    v ∈ cubePencilKernel ξ ↔
      ∀ i, v i = (cubeCoefficient n * (∑ j, ξ j) * ∑ j, v j) / ξ i := by
  rw [mem_cubePencilKernel_iff]
  exact forall_congr' fun i ↦ by rw [eq_div_iff (hz i), mul_comm (v i)]

private def coordinateSum (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' c v := by simp [Finset.mul_sum]

private def zeroSupport {n : ℕ} (ξ : Euclidean n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ i, ξ i ≠ 0 → v i = 0}
  zero_mem' := by simp
  add_mem' hv hw i hi := by simp [hv i hi, hw i hi]
  smul_mem' c v hv i hi := by simp [hv i hi]

private def zeroSupportEquiv {n : ℕ} (ξ : Euclidean n) :
    zeroSupport ξ ≃ₗ[ℝ] (↥(cubeZeroCoordinates ξ) → ℝ) where
  toFun v i := v.val i
  invFun w := ⟨fun i ↦ if hi : i ∈ cubeZeroCoordinates ξ then w ⟨i, hi⟩ else 0,
    by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · exact (v.property i (by simpa using hi)).symm
  right_inv w := by funext i; simp
  map_add' v w := rfl
  map_smul' c v := rfl

private theorem finrank_zeroSupport {n : ℕ} (ξ : Euclidean n) :
    Module.finrank ℝ (zeroSupport ξ) = (cubeZeroCoordinates ξ).card := by
  rw [(zeroSupportEquiv ξ).finrank_eq, Module.finrank_pi, Fintype.card_coe]

/-- The diagonal case of `app:ch_seed:prop:seed-strata`: corank is the number of
zero coordinates when `S_ξ = 0`. -/
theorem finrank_cubePencilKernel_of_sum_eq_zero {n : ℕ} {ξ : Euclidean n}
    (hS : ∑ i, ξ i = 0) :
    Module.finrank ℝ (cubePencilKernel ξ) = (cubeZeroCoordinates ξ).card := by
  have heq : cubePencilKernel ξ = zeroSupport ξ := by
    ext v
    exact mem_cubePencilKernel_iff_of_sum_eq_zero hS v
  rw [heq, finrank_zeroSupport]

/-- The all-nonzero-coordinate case of `app:ch_seed:prop:seed-strata`: the coordinate
sum injects the kernel into the scalar field, so its dimension is at most one. -/
theorem finrank_cubePencilKernel_le_one_of_coordinates_ne_zero {n : ℕ}
    {ξ : Euclidean n} (hz : ∀ i, ξ i ≠ 0) :
    Module.finrank ℝ (cubePencilKernel ξ) ≤ 1 := by
  let f := (coordinateSum n).comp (cubePencilKernel ξ).subtype
  have hf : Function.Injective f := by
    intro v w hvw
    have hv := (mem_cubePencilKernel_iff_of_coordinates_ne_zero hz v.val).mp v.property
    have hw := (mem_cubePencilKernel_iff_of_coordinates_ne_zero hz w.val).mp w.property
    change ∑ i, v.val i = ∑ i, w.val i at hvw
    apply Subtype.ext
    funext i
    rw [hv i, hw i, hvw]
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- Rank-nullity for the zero-sum constraint in `app:ch_seed:prop:seed-strata`:
if `S_ξ ≠ 0` and some coordinate is zero, corank plus one is the number of zeros. -/
theorem finrank_cubePencilKernel_add_one_of_sum_ne_zero {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hS : ∑ i, ξ i ≠ 0) (hz : ∃ i, ξ i = 0) :
    Module.finrank ℝ (cubePencilKernel ξ) + 1 = (cubeZeroCoordinates ξ).card := by
  let f := (coordinateSum n).comp (zeroSupport ξ).subtype
  have hf : Function.Surjective f := by
    obtain ⟨i, hi⟩ := hz
    intro t
    refine ⟨⟨Pi.single i t, ?_⟩, ?_⟩
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact hj hi
      simp [hji]
    · change ∑ j, Pi.single i t j = t
      simp
  have heq : f.ker = (cubePencilKernel ξ).comap (zeroSupport ξ).subtype := by
    ext v
    change (∑ i, v.val i = 0) ↔ v.val ∈ cubePencilKernel ξ
    rw [mem_cubePencilKernel_iff_of_sum_ne_zero hn hS hz]
    exact ⟨fun h ↦ ⟨v.property, h⟩, And.right⟩
  have hle : cubePencilKernel ξ ≤ zeroSupport ξ := by
    intro v hv
    exact ((mem_cubePencilKernel_iff_of_sum_ne_zero hn hS hz v).mp hv).1
  have hdim : Module.finrank ℝ f.ker = Module.finrank ℝ (cubePencilKernel ξ) := by
    rw [heq]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_self,
    hdim, finrank_zeroSupport] at h
  omega

/-- Rank-nullity for the matrix in `app:ch_seed:defn:seed-cube`. -/
theorem cubePencil_rank_add_finrank_kernel {n : ℕ} (ξ : Euclidean n) :
    (cubePencil ξ).rank + Module.finrank ℝ (cubePencilKernel ξ) = n := by
  rw [Matrix.rank, cubePencilKernel, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_pi, Fintype.card_fin]

/-- The numerical form of the corank-two strata in `app:ch_seed:prop:seed-strata`,
with the source's nonzero-covector hypothesis retained. -/
theorem two_le_finrank_cubePencilKernel_iff_card {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (_hξ : ξ ≠ 0) :
    2 ≤ Module.finrank ℝ (cubePencilKernel ξ) ↔
      3 ≤ (cubeZeroCoordinates ξ).card ∨
        (2 ≤ (cubeZeroCoordinates ξ).card ∧ ∑ i, ξ i = 0) := by
  by_cases hS : ∑ i, ξ i = 0
  · rw [finrank_cubePencilKernel_of_sum_eq_zero hS]
    simp only [hS, and_true]
    omega
  · by_cases hz : ∃ i, ξ i = 0
    · have hd := finrank_cubePencilKernel_add_one_of_sum_ne_zero hn hS hz
      simp only [hS, and_false, or_false]
      omega
    · have hz' : ∀ i, ξ i ≠ 0 := by simpa using hz
      have hd := finrank_cubePencilKernel_le_one_of_coordinates_ne_zero hz'
      have hc : cubeZeroCoordinates ξ = ∅ := by ext i; simp [hz' i]
      simp only [hc, Finset.card_empty]
      omega

/-- The corank-at-least-two part of `app:ch_seed:prop:seed-strata`: the nonzero
covector lies in a three-coordinate-zero space or a two-coordinate-zero,
zero-sum space. The node lines belong to the separate corank-one analysis. -/
theorem two_le_finrank_cubePencilKernel_iff {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    2 ≤ Module.finrank ℝ (cubePencilKernel ξ) ↔
      (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0) ∨
      (∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0) := by
  rw [two_le_finrank_cubePencilKernel_iff_card hn hξ]
  have htwo : 2 ≤ (cubeZeroCoordinates ξ).card ↔
      ∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 := by
    rw [show 2 ≤ (cubeZeroCoordinates ξ).card ↔
      1 < (cubeZeroCoordinates ξ).card from by omega, Finset.one_lt_card]
    simp only [mem_cubeZeroCoordinates]
    constructor
    · rintro ⟨i, hi, j, hj, hij⟩
      exact ⟨i, j, hij, hi, hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, hi, j, hj, hij⟩
  have hthree : 3 ≤ (cubeZeroCoordinates ξ).card ↔
      ∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0 := by
    rw [show 3 ≤ (cubeZeroCoordinates ξ).card ↔
      2 < (cubeZeroCoordinates ξ).card from by omega, Finset.two_lt_card_iff]
    simp only [mem_cubeZeroCoordinates]
    constructor
    · rintro ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩
      exact ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
    · rintro ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
      exact ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩
  rw [htwo, hthree]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨⟨i, j, hij, hi, hj⟩, hS⟩
    exact ⟨i, j, hij, hi, hj, hS⟩
  · rintro ⟨i, j, hij, hi, hj, hS⟩
    exact ⟨⟨i, j, hij, hi, hj⟩, hS⟩

/-- Matrix-rank form of the corank-two classification in
`app:ch_seed:prop:seed-strata`, obtained by rank-nullity. -/
theorem cubePencil_rank_add_two_le_iff {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    (cubePencil ξ).rank + 2 ≤ n ↔
      (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0) ∨
      (∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0) := by
  rw [← two_le_finrank_cubePencilKernel_iff hn hξ]
  have h := cubePencil_rank_add_finrank_kernel ξ
  omega

end JanetCartan
