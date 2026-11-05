module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Construction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebraic transversality of detecting reciprocal carriers

The kernel argument in `app:ch_seed:prop:seed-frozen-menu`, Step 3.
The results identify nonproportional incidence and characteristic-normal
vectors; the differential identification and characteristic patch construction
are separate geometric steps.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- The symmetric cubic contraction in `app:ch_seed:prop:seed-frozen-menu`,
Step 3, is symmetric in the two vector inputs. -/
theorem pencil_mulVec_comm {n : ℕ} (k r : Euclidean n) :
    (cubePencil k).mulVec (fun i ↦ r i) = (cubePencil r).mulVec (fun i ↦ k i) := by
  ext i
  simp only [pencil_mulVec_apply]
  ring

/-- Covector scaling of the pencil contraction used in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem pencil_mulVec_smul_left {n : ℕ} (t : ℝ) (k r : Euclidean n) :
    (cubePencil (t • k)).mulVec (fun i ↦ r i) =
      t • (cubePencil k).mulVec (fun i ↦ r i) := by
  ext i
  simp only [pencil_mulVec_apply, PiLp.smul_apply, smul_eq_mul, Pi.smul_apply,
    ← Finset.mul_sum]
  ring

/-- An all-nonzero characteristic has its reciprocal in the pencil kernel
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem reciprocal_mem_kernel {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) :
    (cubePencil r).mulVec (fun i ↦ reciprocal r i) = 0 := by
  rw [pencil_mulVec_eq_zero_iff]
  intro i
  rw [(determinant_eq_zero_iff hr).mp hchar]
  exact mul_inv_cancel₀ (hr i)

/-- The reciprocal characteristic orthogonality used to rule out a zero
incidence gradient (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem pairing_reciprocal_quadratic_eq_zero {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) :
    (∑ i, r i * quadratic (reciprocal r) i) = 0 := by
  have hterm (i : Fin n) : r i * reciprocal r i ^ 2 = reciprocal r i := by
    simp only [reciprocal_apply]
    field_simp
  change (∑ i, r i * ((reciprocal r i)^2 -
    cubeCoefficient n * (∑ j, reciprocal r j)^2)) = 0
  simp only [mul_sub, Finset.sum_sub_distrib, hterm, ← Finset.sum_mul]
  calc
    _ = (∑ i, reciprocal r i) -
      (cubeCoefficient n * (∑ i, r i) * (∑ i, reciprocal r i)) *
        (∑ i, reciprocal r i) := by ring
    _ = 0 := by rw [(determinant_eq_zero_iff hr).mp hchar]; ring

/-- A kernel stress annihilates the incidence vector `M₀(k)r`, which is half
the incidence gradient (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem stress_annihilates_incidence_gradient {n : ℕ} {k s r : Euclidean n}
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    (∑ i, s i * (cubePencil k).mulVec (fun j ↦ r j) i) = 0 := by
  have hsymm : (∑ i, s i * (cubePencil k).mulVec (fun j ↦ r j) i) =
      ∑ i, r i * (cubePencil k).mulVec (fun j ↦ s j) i := by
    simp only [pencil_mulVec_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [← Finset.sum_mul]
      ring
  rw [hsymm, hker]
  simp

/-- Detection forces `M₀(k)r` to be nonzero, as in the transversality argument
of `app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem incidence_gradient_ne_zero {n : ℕ} {k s r : Euclidean n}
    (hk : k ≠ 0) (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hchar : cubeDeterminant r = 0)
    (hdet : (∑ i, s i * quadratic (reciprocal r) i) ≠ 0) :
    (cubePencil k).mulVec (fun i ↦ r i) ≠ 0 := by
  intro hzero
  obtain ⟨C, hC, heq, _⟩ := kernel_eq_smul_reciprocal hr hk
    ((pencil_mulVec_comm k r).symm.trans hzero)
  have hker' : (cubePencil (reciprocal r)).mulVec (fun i ↦ s i) = 0 := by
    rw [heq, pencil_mulVec_smul_left] at hker
    exact (smul_eq_zero.mp hker).resolve_left hC
  obtain ⟨D, _, hsD, _⟩ := kernel_eq_smul_reciprocal
    (fun i ↦ inv_ne_zero (hr i)) hs hker'
  rw [reciprocal_reciprocal] at hsD
  apply hdet
  rw [hsD]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
    pairing_reciprocal_quadratic_eq_zero hr hchar, mul_zero]

/-- The incidence vector is not proportional to the reciprocal characteristic
normal (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem incidence_gradient_not_proportional {n : ℕ} {k s r : Euclidean n}
    (hk : k ≠ 0) (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hchar : cubeDeterminant r = 0)
    (hdet : (∑ i, s i * quadratic (reciprocal r) i) ≠ 0) :
    ¬ ∃ t : ℝ, (cubePencil k).mulVec (fun i ↦ r i) =
      fun i ↦ t * quadratic (reciprocal r) i := by
  rintro ⟨t, ht⟩
  have hann := stress_annihilates_incidence_gradient (r := r) hker
  rw [ht] at hann
  have htzero : t = 0 := by
    have heq : t * (∑ i, s i * quadratic (reciprocal r) i) = 0 := by
      rw [Finset.mul_sum]
      convert hann using 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    exact (mul_eq_zero.mp heq).resolve_right hdet
  apply incidence_gradient_ne_zero hk hs hr hker hchar hdet
  rw [ht]
  ext i
  simp [htzero]

/-- Nonexceptional reciprocal carriers with incidence, detection, nonzero
quadratic normals, and nonproportional incidence/normal vectors, assembling
Steps 1 and the algebra of Step 3 of `app:ch_seed:prop:seed-frozen-menu`.
This statement does not yet identify the vectors with determinant differentials. -/
theorem exists_detecting_reciprocal_with_nonproportional_vectors {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : n = 5 → ¬ ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ r : Euclidean n, (∀ i, r i ≠ 0) ∧
      cubeDeterminant r = 0 ∧ cubeDeterminant (reciprocal r) = 0 ∧
      (∑ i, k i * quadratic r i) = 0 ∧
      (∑ i, s i * quadratic (reciprocal r) i) ≠ 0 ∧
      quadratic r ≠ 0 ∧ quadratic (reciprocal r) ≠ 0 ∧
      (cubePencil k).mulVec (fun i ↦ r i) ≠ 0 ∧
      (¬ ∃ t : ℝ, (cubePencil k).mulVec (fun i ↦ r i) =
        fun i ↦ t * quadratic (reciprocal r) i) ∧
      ∃ (p : Fin 4 ↪ Fin n) (A B : ℝ), A * B * (A - B) ≠ 0 ∧ ∀ i,
        quadratic r i = (if i = p 0 then A else 0) +
          (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
          (if i = p 3 then B else 0) := by
  obtain ⟨r, hr, _, _, hchar, hchar', hinc, hdet, p, A, B, hab, hshape⟩ :=
    exists_detecting_reciprocal_of_nonexceptional hn hk hs hker hnode
  have hqr : quadratic r ≠ 0 := by
    intro hzero
    have hA : A ≠ 0 := by intro h; simp [h] at hab
    apply hA
    have h := hshape (p 0)
    rw [hzero] at h
    simpa only [PiLp.zero_apply, p.injective.eq_iff, ite_true,
      show (0 : Fin 4) ≠ 1 by decide, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, ite_false, add_zero] using h.symm
  have hqrec : quadratic (reciprocal r) ≠ 0 := by
    intro hzero
    apply hdet
    simp [hzero]
  exact ⟨r, hr, hchar, hchar', hinc, hdet, hqr, hqrec,
    incidence_gradient_ne_zero hk hs hr hker hchar hdet,
    incidence_gradient_not_proportional hk hs hr hker hchar hdet,
    p, A, B, hab, hshape⟩

end JanetCartan.CubeCarrier
