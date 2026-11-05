module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Paired
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.CompleteSelection
import Mathlib.Tactic.Ring

/-!
# Constructing detecting reciprocal characteristics from admissible pairs

The algebraic construction in Step 1 of `app:ch_seed:prop:seed-frozen-menu`.
The pair criterion is proved for every nonexceptional kernel direction and
then used to construct the reciprocal characteristics.
-/

@[expose] public noncomputable section

namespace JanetCartan.CubeCarrier

/-- An admissible pair gives reciprocal characteristics with incidence, detection,
and the four-coordinate normal in `app:ch_seed:prop:seed-frozen-menu`, Step 1.
This theorem constructs the carrier; it does not assert existence of the pair. -/
theorem exists_detecting_reciprocal_of_pairCriterion {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} {p : Fin 4 ↪ Fin n} (hp : PairCriterion k s p) :
    ∃ r : Euclidean n, (∀ i, r i ≠ 0) ∧
      (∑ i, r i) = (n : ℝ) - 4 ∧ (∑ i, reciprocal r i) = (n : ℝ) - 4 ∧
      cubeDeterminant r = 0 ∧ cubeDeterminant (reciprocal r) = 0 ∧
      (∑ i, k i * quadratic r i) = 0 ∧
      (∑ i, s i * quadratic (reciprocal r) i) ≠ 0 ∧
      ∃ A B : ℝ, A * B * (A - B) ≠ 0 ∧ ∀ i,
        quadratic r i = (if i = p 0 then A else 0) +
          (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
          (if i = p 3 then B else 0) := by
  obtain ⟨α, β, hinc, hab⟩ := exists_pair_coefficients hp.2
  obtain ⟨t, ht, _, hA, hB, hdet⟩ := exists_small_detection_parameter
    (ε := 1) zero_lt_one hab hp.1
  let r := paired p (Real.sqrt (1+t*α)) (Real.sqrt (1+t*β))
  have hr : ∀ i, r i ≠ 0 := paired_apply_ne_zero p
    (ne_of_gt (Real.sqrt_pos.mpr hA)) (ne_of_gt (Real.sqrt_pos.mpr hB))
  have hsum : (∑ i, r i) = (n : ℝ) - 4 := sum_paired p _ _
  have hsum' : (∑ i, reciprocal r i) = (n : ℝ) - 4 := by
    change (∑ i, reciprocal (paired p (Real.sqrt (1+t*α)) (Real.sqrt (1+t*β))) i) = _
    rw [reciprocal_paired, sum_paired]
  have hchar : cubeDeterminant r = 0 :=
    (determinant_eq_zero_iff_sum_mul_sum hn hr).mpr (by rw [hsum, hsum']; ring)
  refine ⟨r, hr, hsum, hsum', hchar,
    (determinant_reciprocal_eq_zero_iff hr).mpr hchar, ?_, ?_, t*α, t*β, ?_, ?_⟩
  · dsimp [r]
    rw [paired_quadratic_pairing hn]
    simp only [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, add_sub_cancel_left]
    calc
      _ = t * ((k (p 0) + k (p 1)) * α + (k (p 2) + k (p 3)) * β) := by ring
      _ = 0 := by rw [hinc, mul_zero]
  · dsimp [r]
    rw [paired_sqrt_reciprocal_pairing hn p α β t hA hB s]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (ne_of_gt ht) hdet))
      (mul_ne_zero (ne_of_gt hA) (ne_of_gt hB))
  · have heq : (t*α)*(t*β)*(t*α-t*β) = t^3 * (α*β*(α-β)) := by ring
    rw [heq]
    exact mul_ne_zero (pow_ne_zero 3 (ne_of_gt ht)) hab
  · intro i
    dsimp [r]
    rw [quadratic_paired_apply hn]
    simp only [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, add_sub_cancel_left]

/-- The nonexceptional reciprocal detecting carriers in
`app:ch_seed:prop:seed-frozen-menu`, Step 1, with pair existence discharged.
The exceptional node directions in dimension five belong to Step 2. -/
theorem exists_detecting_reciprocal_of_nonexceptional {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : n = 5 → ¬ ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ r : Euclidean n, (∀ i, r i ≠ 0) ∧
      (∑ i, r i) = (n : ℝ) - 4 ∧ (∑ i, reciprocal r i) = (n : ℝ) - 4 ∧
      cubeDeterminant r = 0 ∧ cubeDeterminant (reciprocal r) = 0 ∧
      (∑ i, k i * quadratic r i) = 0 ∧
      (∑ i, s i * quadratic (reciprocal r) i) ≠ 0 ∧
      ∃ (p : Fin 4 ↪ Fin n) (A B : ℝ), A * B * (A - B) ≠ 0 ∧ ∀ i,
        quadratic r i = (if i = p 0 then A else 0) +
          (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
          (if i = p 3 then B else 0) := by
  obtain ⟨p, hp⟩ := exists_pairCriterion_of_nonexceptional hn hk hs hker hnode
  obtain ⟨r, hr, hsum, hsum', hchar, hchar', hinc, hdet, A, B, hab, hshape⟩ :=
    exists_detecting_reciprocal_of_pairCriterion hn hp
  exact ⟨r, hr, hsum, hsum', hchar, hchar', hinc, hdet, p, A, B, hab, hshape⟩

end JanetCartan.CubeCarrier
