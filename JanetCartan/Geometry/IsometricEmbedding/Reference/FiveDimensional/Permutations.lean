module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FiveDimensional.Geometry
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
/-!
# Permuting the exceptional carrier

Coordinate transport for Step 2 of `app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiveDimensional

/-- Coordinate transport of the explicit carrier (`app:ch_seed:prop:seed-frozen-menu`). -/
def reindex (σ : Equiv.Perm (Fin 5)) (x : Euclidean 5) : Euclidean 5 :=
  WithLp.toLp 2 fun i ↦ x (σ i)

/-- Coordinate sums are permutation invariant (`app:ch_seed:prop:seed-frozen-menu`). -/
theorem sum_reindex (σ : Equiv.Perm (Fin 5)) (x : Euclidean 5) :
    (∑ i, reindex σ x i) = ∑ i, x i := by
  exact Equiv.sum_comp σ (fun i ↦ x i)

/-- The cube quadratic map commutes with permutations (`app:ch_seed:defn:seed-cube`). -/
theorem quadratic_reindex (σ : Equiv.Perm (Fin 5)) (x : Euclidean 5) :
    quadratic (reindex σ x) = reindex σ (quadratic x) := by
  ext i
  change x (σ i) ^ 2 - (∑ j, reindex σ x j) ^ 2 =
    x (σ i) ^ 2 - (∑ j, x j) ^ 2
  rw [sum_reindex]

/-- Pairings are invariant under coordinate permutations (`app:ch_seed:prop:seed-frozen-menu`). -/
theorem pairing_reindex (σ : Equiv.Perm (Fin 5)) (x y : Euclidean 5) :
    (∑ i, reindex σ x i * reindex σ y i) = ∑ i, x i * y i := by
  exact Equiv.sum_comp σ (fun i ↦ x i * y i)

/-- Incidence and nonzero detection for every permuted node line
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem permuted_node_detection (σ : Equiv.Perm (Fin 5)) (t : ℝ) (ht : t ≠ 0)
    (s : Euclidean 5)
    (hs : (cubePencil (t • reindex σ node)).mulVec (fun i ↦ s i) = 0) (hne : s ≠ 0) :
    (∑ i, (t • reindex σ node) i * quadratic (reindex σ reciprocalCarrier) i) = 0 ∧
      (∑ i, s i * quadratic (reindex σ carrier) i) ≠ 0 := by
  have heq : s = reindex σ (reindex σ.symm s) := by ext i; simp [reindex]
  have hk : (cubePencil (t • node)).mulVec (fun i ↦ reindex σ.symm s i) = 0 := by
    ext i
    have hi := congr_fun hs (σ.symm i)
    rw [pencil_mulVec_apply] at hi ⊢
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_reindex] at hi ⊢
    simpa [reindex] using hi
  constructor
  · rw [quadratic_reindex]
    simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [pairing_reindex, node_pairings.1, mul_zero]
  · rw [quadratic_reindex, heq, pairing_reindex]
    apply node_line_detection t ht _ hk
    intro h
    apply hne
    rw [h] at heq
    ext i
    simpa [reindex] using congrArg (fun x : Euclidean 5 ↦ x i) heq

/-- Permutation covariance of the pencil (`app:ch_seed:defn:seed-cube`). -/
theorem pencil_reindex (σ : Equiv.Perm (Fin 5)) (x : Euclidean 5) :
    cubePencil (reindex σ x) = (cubePencil x).reindex σ.symm σ.symm := by
  ext i j
  simp only [cubePencil, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, reindex, PiLp.toLp_apply, Equiv.apply_eq_iff_eq]
  rw [Equiv.sum_comp σ]

/-- Permutation invariance of the characteristic polynomial (`app:ch_seed:defn:seed-cube`). -/
theorem determinant_reindex (σ : Equiv.Perm (Fin 5)) (x : Euclidean 5) :
    cubeDeterminant (reindex σ x) = cubeDeterminant x := by
  unfold cubeDeterminant
  rw [pencil_reindex, Matrix.det_reindex_self]

/-- The permuted carriers are simple (`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_reindex_ranks (σ : Equiv.Perm (Fin 5)) :
    (cubePencil (reindex σ carrier)).rank = 4 ∧
      (cubePencil (reindex σ reciprocalCarrier)).rank = 4 := by
  simp only [pencil_reindex, Matrix.rank_reindex]
  exact carrier_ranks

/-- The permuted carriers are characteristic (`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_reindex_characteristic (σ : Equiv.Perm (Fin 5)) :
    cubeDeterminant (reindex σ carrier) = 0 ∧
      cubeDeterminant (reindex σ reciprocalCarrier) = 0 := by
  rw [determinant_reindex, determinant_reindex]
  exact ⟨carrier_characteristic, reciprocalCarrier_characteristic⟩

/-- The permuted carriers remain reciprocals (`app:ch_seed:eq:seed-five-node-carrier`). -/
theorem carrier_reindex_reciprocal (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    reindex σ carrier i * reindex σ reciprocalCarrier i = 1 :=
  carrier_mul_reciprocal (σ i)

/-- Every cube node in dimension five is a permutation of the displayed node
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem exists_node_reindex (a b : Fin 5) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 5), reindex σ node = cubeVector a b := by
  have hinj : Function.Injective (![a, b] : Fin 2 → Fin 5) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (![a, b] : Fin 2 → Fin 5) (![3, 4] : Fin 2 → Fin 5) hinj
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  have ha : σ a = 3 := hσ 0
  have hb : σ b = 4 := hσ 1
  refine ⟨σ, ?_⟩
  ext i
  simp only [reindex, node_eq_cubeVector, cubeVector, PiLp.toLp_apply]
  rw [← ha, ← hb]
  simp only [Equiv.apply_eq_iff_eq]
end JanetCartan.FiveDimensional

