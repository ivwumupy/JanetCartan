module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal algebra for detecting cube carriers

The algebra in Step 1 of Proposition `app:ch_seed:prop:seed-frozen-menu`.
These results do not use the unfinished geometric statements in `Reference`.
-/

@[expose] public noncomputable section

namespace JanetCartan.CubeCarrier

/-- Coordinate inversion in Step 1 of `app:ch_seed:prop:seed-frozen-menu`.
Its use as a reciprocal characteristic requires nonzero coordinates. -/
def reciprocal {n : ℕ} (r : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 (fun i ↦ (r i)⁻¹)

/-- The quadratic stress vector `q₀` in `app:ch_seed:prop:seed-frozen-menu`. -/
def quadratic {n : ℕ} (r : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 (fun i ↦ r i ^ 2 - cubeCoefficient n * (∑ j, r j) ^ 2)

@[simp] theorem reciprocal_apply {n : ℕ} (r : Euclidean n) (i : Fin n) :
    reciprocal r i = (r i)⁻¹ := rfl

@[simp] theorem reciprocal_reciprocal {n : ℕ} (r : Euclidean n) :
    reciprocal (reciprocal r) = r := by
  ext i
  exact inv_inv (r i)

/-- The coordinate kernel identity `app:ch_seed:eq:seed-kernel-pair`. -/
theorem pencil_mulVec_apply {n : ℕ} (k s : Euclidean n) (i : Fin n) :
    (cubePencil k).mulVec (fun j ↦ s j) i =
      k i * s i - cubeCoefficient n * (∑ j, k j) * (∑ j, s j) := by
  simp [Matrix.mulVec, dotProduct, cubePencil, sub_mul, Finset.sum_sub_distrib,
    ite_mul, ← Finset.mul_sum]

/-- The kernel condition written coordinatewise, as in
`app:ch_seed:eq:seed-kernel-pair`. -/
theorem pencil_mulVec_eq_zero_iff {n : ℕ} (k s : Euclidean n) :
    (cubePencil k).mulVec (fun i ↦ s i) = 0 ↔
      ∀ i, k i * s i = cubeCoefficient n * (∑ j, k j) * (∑ j, s j) := by
  simp only [funext_iff, pencil_mulVec_apply, Pi.zero_apply, sub_eq_zero]

/-- A zero coordinate of `k` confines any kernel vector to its zero coordinates
(Step 1 of `app:ch_seed:prop:seed-frozen-menu`). -/
theorem kernel_supported_on_zeros {n : ℕ} {k s : Euclidean n}
    (hs : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hz : ∃ j, k j = 0) : ∀ i, k i ≠ 0 → s i = 0 := by
  obtain ⟨j, hj⟩ := hz
  have h := (pencil_mulVec_eq_zero_iff k s).mp hs
  have hc : cubeCoefficient n * (∑ l, k l) * (∑ l, s l) = 0 := by
    simpa [hj] using (h j).symm
  intro i hi
  exact (mul_eq_zero.mp ((h i).trans hc)).resolve_left hi

/-- With no zero coordinates a nonzero kernel vector is a nonzero multiple of
`k⁻¹` (Step 1 of `app:ch_seed:prop:seed-frozen-menu`). -/
theorem kernel_eq_smul_reciprocal {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    ∃ C : ℝ, C ≠ 0 ∧ s = C • reciprocal k ∧ (∑ i, k i) ≠ 0 := by
  let C := cubeCoefficient n * (∑ i, k i) * (∑ i, s i)
  have h := (pencil_mulVec_eq_zero_iff k s).mp hker
  have heq : s = C • reciprocal k := by
    ext i
    change s i = C * (k i)⁻¹
    change s i = (cubeCoefficient n * (∑ j, k j) * (∑ j, s j)) * (k i)⁻¹
    rw [← h i]
    field_simp [hk i]
  have hC : C ≠ 0 := by
    intro hC
    apply hs
    simpa [hC] using heq
  refine ⟨C, hC, heq, ?_⟩
  intro hsum
  apply hC
  simp [C, hsum]

/-- The determinant formula factored using reciprocal coordinates; this is the
first calculation of `app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem determinant_factor {n : ℕ} {r : Euclidean n} (hr : ∀ i, r i ≠ 0) :
    cubeDeterminant r = (∏ i, r i) *
      (1 - cubeCoefficient n * (∑ i, r i) * (∑ i, reciprocal r i)) := by
  have hterm (i : Fin n) :
      (∏ j, r j) * (r i)⁻¹ = ∏ j ∈ Finset.univ.erase i, r j := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ r j) (Finset.mem_univ i)]
    field_simp [hr i]
  have hsum : (∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, r j) =
      (∏ j, r j) * (∑ i, reciprocal r i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ (hterm i).symm)
  rw [cubeDeterminant_eq, hsum]
  ring

/-- Reciprocal characterization of the cube characteristic equation in Step 1
of `app:ch_seed:prop:seed-frozen-menu`. -/
theorem determinant_eq_zero_iff {n : ℕ} {r : Euclidean n} (hr : ∀ i, r i ≠ 0) :
    cubeDeterminant r = 0 ↔
      cubeCoefficient n * (∑ i, r i) * (∑ i, reciprocal r i) = 1 := by
  rw [determinant_factor hr, mul_eq_zero]
  have hp : (∏ i, r i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hr i)
  simp only [hp, false_or, sub_eq_zero]
  exact eq_comm

/-- Coordinate inversion preserves the all-nonzero characteristic locus in
`app:ch_seed:prop:seed-frozen-menu`. -/
theorem determinant_reciprocal_eq_zero_iff {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) :
    cubeDeterminant (reciprocal r) = 0 ↔ cubeDeterminant r = 0 := by
  rw [determinant_eq_zero_iff (fun i ↦ inv_ne_zero (hr i)), determinant_eq_zero_iff hr,
    reciprocal_reciprocal]
  simp only [mul_assoc, mul_comm]

/-- The exact `Sᵣ Sᵣ⁻¹ = (n-4)²` condition from Step 1 of
`app:ch_seed:prop:seed-frozen-menu`, with the manuscript's dimension hypothesis. -/
theorem determinant_eq_zero_iff_sum_mul_sum {n : ℕ} (hn : 5 ≤ n)
    {r : Euclidean n} (hr : ∀ i, r i ≠ 0) :
    cubeDeterminant r = 0 ↔
      (∑ i, r i) * (∑ i, reciprocal r i) = ((n : ℝ) - 4) ^ 2 := by
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [determinant_eq_zero_iff hr, cubeCoefficient]
  constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith [h]

/-- The explicit admissible coefficients following
`app:ch_seed:eq:seed-pair-criterion`. -/
theorem exists_pair_coefficients {K L : ℝ}
    (h : (K = 0 ∧ L = 0) ∨ K * L * (K + L) ≠ 0) :
    ∃ α β : ℝ, K * α + L * β = 0 ∧ α * β * (α - β) ≠ 0 := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact ⟨1, 2, by norm_num, by norm_num⟩
  · refine ⟨L, -K, by ring, ?_⟩
    have heq : L * -K * (L - -K) = -(K * L * (K + L)) := by ring
    rw [heq]
    exact neg_ne_zero.mpr h

/-- The numerator in the detecting pairing is not the zero polynomial
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem detection_coefficients_not_both_zero {α β S T : ℝ}
    (hab : α * β * (α - β) ≠ 0) (hST : S ≠ 0 ∨ T ≠ 0) :
    α * S + β * T ≠ 0 ∨ α * β * (S + T) ≠ 0 := by
  by_contra h
  push Not at h
  have hab' : α * β ≠ 0 := fun hzero ↦ hab (by rw [hzero, zero_mul])
  have hsum : S + T = 0 := (mul_eq_zero.mp h.2).resolve_left hab'
  have hdiff : α - β ≠ 0 := fun hzero ↦ hab (by rw [hzero, mul_zero])
  have hlinear : (α - β) * S = 0 := by
    calc
      (α - β) * S = (α * S + β * T) - β * (S + T) := by ring
      _ = 0 := by rw [h.1, hsum]; ring
  have hS : S = 0 := (mul_eq_zero.mp hlinear).resolve_left hdiff
  rcases hST with hST | hST <;> apply hST <;> linarith

end JanetCartan.CubeCarrier
