module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FiveDimensional.Algebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Detection and bad-normal exclusions

The exceptional carrier in `app:ch_seed:prop:seed-frozen-menu`, Steps 2–3.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiveDimensional

/-- Homogeneity of the cube pencil (`app:ch_seed:defn:seed-cube`). -/
theorem pencil_smul_apply (t : ℝ) (x : Euclidean 5) (i j : Fin 5) :
    cubePencil (t • x) i j = t * cubePencil x i j := by
  simp only [cubePencil, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

/-- The kernel on every nonzero point of the exceptional node line
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem node_line_kernel (t : ℝ) (ht : t ≠ 0) (s : Euclidean 5) :
    (cubePencil (t • node)).mulVec (fun i ↦ s i) = 0 ↔ ∃ a : ℝ, s = a • node := by
  have heq : cubePencil (t • node) = t • cubePencil node := by
    ext i j; exact pencil_smul_apply t node i j
  rw [heq, Matrix.smul_mulVec, smul_eq_zero_iff_right ht]
  exact node_kernel s

/-- The explicit carrier detects every nonzero node-kernel stress
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem node_line_detection (t : ℝ) (ht : t ≠ 0) (s : Euclidean 5)
    (hs : (cubePencil (t • node)).mulVec (fun i ↦ s i) = 0) (hne : s ≠ 0) :
    (∑ i, s i * quadratic carrier i) ≠ 0 := by
  obtain ⟨a, rfl⟩ := (node_line_kernel t ht s).mp hs
  have ha : a ≠ 0 := by intro h; apply hne; rw [h, zero_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [node_pairings.2]
  exact mul_ne_zero ha (by norm_num)

/-- The reciprocal normal has exactly four nonzero coordinates
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_zero_iff (i : Fin 5) : quadratic reciprocalCarrier i = 0 ↔ i = 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [quadratic_reciprocalCarrier]
  fin_cases i <;> norm_num <;> nlinarith

/-- Only coordinates zero and one of the reciprocal normal coincide
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_eq_iff (i j : Fin 5) :
    quadratic reciprocalCarrier i = quadratic reciprocalCarrier j ↔
      i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [quadratic_reciprocalCarrier]
  fin_cases i <;> fin_cases j <;> norm_num <;> nlinarith

/-- No three distinct coordinates of the reciprocal normal coincide
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_no_three_equal (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬(quadratic reciprocalCarrier i = quadratic reciprocalCarrier j ∧
      quadratic reciprocalCarrier i = quadratic reciprocalCarrier k) := by
  simp only [normal_eq_iff]
  omega

/-- Half the incidence gradient at the reciprocal carrier
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem node_incidence_vector :
    (cubePencil node).mulVec (fun i ↦ reciprocalCarrier i) =
      ![1 / 2, 1 / 2, -1, -Real.sqrt 3 / 2, Real.sqrt 3 / 2] := by
  ext i
  rw [pencil_mulVec_apply, carrier_sums.1, carrier_sums.2.2]
  fin_cases i <;> norm_num [node, reciprocalCarrier] <;> ring

/-- The incidence gradient and characteristic normal in reciprocal coordinates
are independent (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem incidence_normals_independent (t a b : ℝ) (ht : t ≠ 0)
    (h : ∀ i, a * (2 * (cubePencil (t • node)).mulVec (fun j ↦ reciprocalCarrier j) i) +
      b * quadratic carrier i = 0) : a = 0 ∧ b = 0 := by
  have heq : cubePencil (t • node) = t • cubePencil node := by
    ext i j; exact pencil_smul_apply t node i j
  have h0 := h 0
  have h2 := h 2
  rw [heq, Matrix.smul_mulVec, node_incidence_vector, quadratic_carrier] at h0 h2
  norm_num at h0 h2
  have ha : a = 0 := h2.resolve_right ht
  exact ⟨ha, by rw [ha] at h0; linarith⟩
/-- A nonzero normal coordinate outside any coordinate triple
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_has_outside_triple (i j k : Fin 5) :
    ∃ l : Fin 5, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ quadratic reciprocalCarrier l ≠ 0 := by
  simp only [ne_eq, normal_zero_iff]
  revert i j k
  decide

/-- Unequal normal coordinates outside any coordinate pair
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_has_unequal_outside_pair (i j : Fin 5) :
    ∃ a b : Fin 5, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧
      quadratic reciprocalCarrier a ≠ quadratic reciprocalCarrier b := by
  simp only [ne_eq, normal_eq_iff]
  revert i j
  decide

/-- A vector in each L_ijl with nonzero normal pairing. Thus the normal
is outside every L_ijl perpendicular (`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_triple_witness (i j k : Fin 5) :
    ∃ x : Euclidean 5, x i = 0 ∧ x j = 0 ∧ x k = 0 ∧
      (∑ l, x l * quadratic reciprocalCarrier l) ≠ 0 := by
  obtain ⟨l, hli, hlj, hlk, hl⟩ := normal_has_outside_triple i j k
  refine ⟨EuclideanSpace.single l 1, ?_, ?_, ?_, ?_⟩
  · simp [Ne.symm hli]
  · simp [Ne.symm hlj]
  · simp [Ne.symm hlk]
  · simpa using hl

/-- A vector in each L_ijS with nonzero normal pairing. Thus the normal
is outside every L_ijS perpendicular (`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem normal_pair_sum_witness (i j : Fin 5) :
    ∃ x : Euclidean 5, x i = 0 ∧ x j = 0 ∧ (∑ l, x l) = 0 ∧
      (∑ l, x l * quadratic reciprocalCarrier l) ≠ 0 := by
  obtain ⟨a, b, hai, haj, hbi, hbj, hab⟩ := normal_has_unequal_outside_pair i j
  refine ⟨EuclideanSpace.single a 1 - EuclideanSpace.single b 1, ?_, ?_, ?_, ?_⟩
  · simp [Ne.symm hai, Ne.symm hbi]
  · simp [Ne.symm haj, Ne.symm hbj]
  · simp [Finset.sum_sub_distrib]
  · simpa [sub_mul, Finset.sum_sub_distrib] using sub_ne_zero.mpr hab

/-- Incidence holds on the entire exceptional node line
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem node_line_incidence (t : ℝ) :
    (∑ i, (t • node) i * quadratic reciprocalCarrier i) = 0 := by
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
    node_pairings.1, mul_zero]

/-- The exact squared detection gap on the node kernel
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem node_line_detection_gap (t : ℝ) (ht : t ≠ 0) (s : Euclidean 5)
    (hs : (cubePencil (t • node)).mulVec (fun i ↦ s i) = 0) :
    (∑ i, s i * quadratic carrier i) ^ 2 = (36 / 5) * ‖s‖ ^ 2 := by
  obtain ⟨a, rfl⟩ := (node_line_kernel t ht s).mp hs
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [node_pairings.2]
  norm_num [node, Fin.sum_univ_succ]
  ring

/-- Both displayed characteristic normals are nonzero
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_normals_ne_zero : quadratic carrier ≠ 0 ∧ quadratic reciprocalCarrier ≠ 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Euclidean 5 ↦ x 0) h
    rw [quadratic_carrier] at h0
    norm_num at h0
  · intro h
    have h0 := congrArg (fun x : Euclidean 5 ↦ x 0) h
    rw [quadratic_reciprocalCarrier] at h0
    norm_num at h0

end JanetCartan.FiveDimensional
