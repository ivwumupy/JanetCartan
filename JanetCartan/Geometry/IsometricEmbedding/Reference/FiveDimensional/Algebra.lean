module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The exceptional five-dimensional carrier

The explicit calculation in Step 2 of Proposition
`app:ch_seed:prop:seed-frozen-menu`. All coordinates use the existing cube pencil.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiveDimensional

/-- The node direction in `app:ch_seed:eq:seed-five-node-carrier`. -/
def node : Euclidean 5 := WithLp.toLp 2 ![1, 1, 1, -1, -1]

/-- The reciprocal carrier in `app:ch_seed:eq:seed-five-node-carrier`. -/
def reciprocalCarrier : Euclidean 5 :=
  WithLp.toLp 2 ![1, 1, -(1 / 2), (-1 + Real.sqrt 3) / 2, (-1 - Real.sqrt 3) / 2]

/-- The carrier in `app:ch_seed:eq:seed-five-node-carrier`. -/
def carrier : Euclidean 5 :=
  WithLp.toLp 2 ![1, 1, -2, 1 + Real.sqrt 3, 1 - Real.sqrt 3]

/-- The quadratic map of `app:ch_seed:defn:seed-cube`, specialized to dimension five. -/
def quadratic (x : Euclidean 5) : Euclidean 5 :=
  WithLp.toLp 2 fun i ↦ x i ^ 2 - (∑ j, x j) ^ 2

/-- The quadratic map is the existing cube pencil applied to its argument
(`app:ch_seed:defn:seed-cube`). -/
theorem quadratic_eq_pencil (x : Euclidean 5) (i : Fin 5) :
    quadratic x i = (cubePencil x).mulVec (fun j ↦ x j) i := by
  norm_num [quadratic, cubePencil, cubeCoefficient, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sq]

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Coordinate sums from Step 2 of `app:ch_seed:prop:seed-frozen-menu`. -/
theorem carrier_sums :
    (∑ i, reciprocalCarrier i) = 1 / 2 ∧ (∑ i, carrier i) = 2 ∧
      (∑ i, node i) = 1 := by
  norm_num [reciprocalCarrier, carrier, node, Fin.sum_univ_succ]
  ring

/-- The two displayed vectors really are coordinatewise reciprocals
(`app:ch_seed:eq:seed-five-node-carrier`). -/
theorem carrier_mul_reciprocal (i : Fin 5) : carrier i * reciprocalCarrier i = 1 := by
  fin_cases i <;> norm_num [carrier, reciprocalCarrier] <;> nlinarith [sqrt_three_sq]

/-- Both carriers have all coordinates nonzero
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_coordinates_ne_zero (i : Fin 5) :
    carrier i ≠ 0 ∧ reciprocalCarrier i ≠ 0 := by
  have h := carrier_mul_reciprocal i
  exact ⟨fun hi ↦ by rw [hi, zero_mul] at h; norm_num at h,
    fun hi ↦ by rw [hi, mul_zero] at h; norm_num at h⟩

/-- Reciprocal identity in `app:ch_seed:eq:seed-five-node-carrier`. -/
theorem carrier_eq_inv (i : Fin 5) : carrier i = (reciprocalCarrier i)⁻¹ := by
  apply mul_right_cancel₀ (carrier_coordinates_ne_zero i).2
  rw [carrier_mul_reciprocal, inv_mul_cancel₀ (carrier_coordinates_ne_zero i).2]

/-- The first normal displayed in Step 2 of `app:ch_seed:prop:seed-frozen-menu`. -/
theorem quadratic_reciprocalCarrier :
    quadratic reciprocalCarrier =
      WithLp.toLp 2 ![3 / 4, 3 / 4, 0, 3 / 4 - Real.sqrt 3 / 2,
        3 / 4 + Real.sqrt 3 / 2] := by
  ext i
  simp only [quadratic, carrier_sums.1]
  fin_cases i <;> norm_num [reciprocalCarrier] <;> nlinarith [sqrt_three_sq]

/-- The second normal displayed in Step 2 of `app:ch_seed:prop:seed-frozen-menu`. -/
theorem quadratic_carrier :
    quadratic carrier = WithLp.toLp 2 ![-3, -3, 0, 2 * Real.sqrt 3, -2 * Real.sqrt 3] := by
  ext i
  simp only [quadratic, carrier_sums.2.1]
  fin_cases i <;> norm_num [carrier] <;> nlinarith [sqrt_three_sq]

/-- Incidence and detection at the exceptional node
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem node_pairings :
    (∑ i, node i * quadratic reciprocalCarrier i) = 0 ∧
      (∑ i, node i * quadratic carrier i) = -6 := by
  rw [quadratic_reciprocalCarrier, quadratic_carrier]
  norm_num [node, Fin.sum_univ_succ]
  ring

/-- Coordinate equation for the cube pencil (`app:ch_seed:eq:seed-kernel-pair`). -/
theorem pencil_mulVec_apply (x s : Euclidean 5) (i : Fin 5) :
    (cubePencil x).mulVec (fun j ↦ s j) i = x i * s i - (∑ j, x j) * ∑ j, s j := by
  norm_num [cubePencil, cubeCoefficient, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]

private theorem pencil_kernel_iff (x y : Euclidean 5)
    (hxy : ∀ i, x i * y i = 1) (hsum : (∑ i, x i) * (∑ i, y i) = 1)
    (s : Euclidean 5) :
    (cubePencil x).mulVec (fun i ↦ s i) = 0 ↔ ∃ t : ℝ, s = t • y := by
  constructor
  · intro h
    refine ⟨(∑ i, x i) * ∑ i, s i, ?_⟩
    ext i
    have hi := congr_fun h i
    rw [pencil_mulVec_apply] at hi
    change s i = ((∑ i, x i) * ∑ i, s i) * y i
    have heq : x i * s i = (∑ i, x i) * ∑ i, s i := sub_eq_zero.mp hi
    rw [← heq]
    calc
      s i = (x i * y i) * s i := by rw [hxy i, one_mul]
      _ = x i * s i * y i := by ring
  · rintro ⟨t, rfl⟩
    ext i
    rw [pencil_mulVec_apply]
    simp only [PiLp.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← Finset.mul_sum]
    calc
      _ = t * (x i * y i - (∑ i, x i) * ∑ i, y i) := by ring
      _ = 0 := by rw [hxy i, hsum]; ring

/-- The carrier kernel is precisely the reciprocal line (`app:ch_seed:prop:seed-frozen-menu`). -/
theorem carrier_kernel (s : Euclidean 5) :
    (cubePencil carrier).mulVec (fun i ↦ s i) = 0 ↔
      ∃ t : ℝ, s = t • reciprocalCarrier :=
  pencil_kernel_iff _ _ carrier_mul_reciprocal (by rw [carrier_sums.1, carrier_sums.2.1]; norm_num) s

/-- The reciprocal carrier kernel is precisely the carrier line (`app:ch_seed:prop:seed-frozen-menu`). -/
theorem reciprocalCarrier_kernel (s : Euclidean 5) :
    (cubePencil reciprocalCarrier).mulVec (fun i ↦ s i) = 0 ↔
      ∃ t : ℝ, s = t • carrier :=
  pencil_kernel_iff _ _ (fun i ↦ by rw [mul_comm]; exact carrier_mul_reciprocal i)
    (by rw [carrier_sums.1, carrier_sums.2.1]; norm_num) s

/-- The exceptional node has kernel equal to its own line (`app:ch_seed:prop:seed-frozen-menu`). -/
theorem node_kernel (s : Euclidean 5) :
    (cubePencil node).mulVec (fun i ↦ s i) = 0 ↔ ∃ t : ℝ, s = t • node :=
  pencil_kernel_iff _ _ (by intro i; fin_cases i <;> norm_num [node])
    (by rw [carrier_sums.2.2]; norm_num) s

/-- The explicit carrier is characteristic (`app:ch_seed:eq:seed-five-node-carrier`). -/
theorem carrier_characteristic : cubeDeterminant carrier = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    ((carrier_kernel reciprocalCarrier).mpr ⟨1, by simp⟩) (i := 0)
  norm_num [reciprocalCarrier]

/-- The reciprocal carrier is characteristic (`app:ch_seed:eq:seed-five-node-carrier`). -/
theorem reciprocalCarrier_characteristic : cubeDeterminant reciprocalCarrier = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    ((reciprocalCarrier_kernel carrier).mpr ⟨1, by simp⟩) (i := 0)
  norm_num [carrier]

private theorem rank_four_of_kernel (x y : Euclidean 5) (hy : y 0 ≠ 0)
    (hker : ∀ s : Euclidean 5,
      (cubePencil x).mulVec (fun i ↦ s i) = 0 ↔ ∃ t : ℝ, s = t • y) :
    (cubePencil x).rank = 4 := by
  have hk : (cubePencil x).mulVecLin.ker =
      Submodule.span ℝ {fun i ↦ y i} := by
    ext s
    change (cubePencil x).mulVec s = 0 ↔ _
    rw [hker (WithLp.toLp 2 s), Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, (congrArg (fun z : Euclidean 5 ↦ fun i ↦ z i) ht).symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, by ext i; exact (congr_fun ht i).symm⟩
  have hdim := (cubePencil x).mulVecLin.finrank_range_add_finrank_ker
  rw [hk, finrank_span_singleton (by intro h; exact hy (congr_fun h 0)),
    Module.finrank_pi, Fintype.card_fin] at hdim
  change (cubePencil x).rank + 1 = 5 at hdim
  omega

/-- Both characteristics are simple: their pencils have rank four
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_ranks : (cubePencil carrier).rank = 4 ∧
    (cubePencil reciprocalCarrier).rank = 4 :=
  ⟨rank_four_of_kernel _ _ (carrier_coordinates_ne_zero 0).2 carrier_kernel,
    rank_four_of_kernel _ _ (carrier_coordinates_ne_zero 0).1 reciprocalCarrier_kernel⟩

/-- The displayed node is the cube node with negative coordinates three and four
(`app:ch_seed:eq:seed-five-node-carrier`; coordinates are zero based). -/
theorem node_eq_cubeVector : node = cubeVector (3 : Fin 5) 4 := by
  ext i
  fin_cases i <;> norm_num [node, cubeVector]

end JanetCartan.FiveDimensional
