module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.Definitions
public import Mathlib.Logic.Equiv.Fintype

/-!
# Operator norms of symmetric jets from Cartesian evaluations

For the derivative norm in `app:ch_regular_base:eq:ball-extension-sobolev`,
multilinearity bounds an operator norm by the sum of its evaluations on basis
tuples. Permutation symmetry identifies each such evaluation with the canonical
list for its coordinate multiplicities. Bounding these evaluations by the square
root of the Cartesian energy gives a uniform bound for the sum of squared jet
norms. No dimension or positive-order assumption is needed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.BallExtension

/-- Basis expansion controls the operator norm, as needed for the derivative
norm in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
private theorem norm_le_basis_sum {n j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℝ) :
    ‖A‖ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv : v = fun k ↦ ∑ i, b.repr (v k) i • b i := by
    funext k
    exact (b.sum_repr (v k)).symm
  calc
    ‖A v‖ = ‖∑ a : Fin j → Fin n, (∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin j → Fin n, ‖(∏ k, b.repr (v k) (a k)) •
        A (fun k ↦ b (a k))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin j → Fin n, ‖A (fun k ↦ b (a k))‖ * ∏ k, ‖v k‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro k _
      exact (PiLp.norm_apply_le (b.repr (v k)) (a k)).trans_eq (b.repr.norm_map _)
    _ = _ := (Finset.sum_mul ..).symm

private theorem count_ofFn_eq_sum {n j : ℕ} (a : Fin j → Fin n) (i : Fin n) :
    (List.ofFn a).count i = ∑ k, if a k = i then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, ih]
    simp only [beq_iff_eq]
    exact Nat.add_comm ..

private theorem count_ofFn_eq_card {n j : ℕ} (a : Fin j → Fin n) (i : Fin n) :
    (List.ofFn a).count i = Fintype.card {k // a k = i} := by
  rw [count_ofFn_eq_sum, Fintype.card_subtype, Finset.card_filter]

/-- Equal coordinate multiplicities give a permutation of the slots; this is the
combinatorial step in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
private theorem perm_of_counts {n j : ℕ} (a b : Fin j → Fin n)
    (h : ∀ i, (List.ofFn a).count i = (List.ofFn b).count i) :
    ∃ σ : Equiv.Perm (Fin j), b ∘ σ = a := by
  classical
  let e (i : Fin n) : {k // a k = i} ≃ {k // b k = i} :=
    Fintype.equivOfCardEq (by simpa only [← count_ofFn_eq_card] using h i)
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

private theorem sum_counts {n j : ℕ} (a : Fin j → Fin n) :
    ∑ i, (List.ofFn a).count i = j := by
  simp_rw [count_ofFn_eq_sum]
  rw [Finset.sum_comm]
  simp

private theorem symmetric_basis_eq_list {n m j : ℕ}
    (A : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℝ)
    (hsym : ∀ j ≤ m, ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
      ∀ σ : Equiv.Perm (Fin j), A j (v ∘ σ) = A j v)
    (hj : j ≤ m) (a : Fin j → Fin n) (l : List (Fin n))
    (hl : l.length = j) (hc : ∀ i, l.count i = (List.ofFn a).count i) :
    A j (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k)) =
      A l.length (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (l.get k)) := by
  subst j
  obtain ⟨σ, hσ⟩ := perm_of_counts a l.get (fun i ↦ by
    simpa only [List.ofFn_get] using (hc i).symm)
  have hv : (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k)) =
      (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (l.get k)) ∘ σ := by
    funext k
    exact congrArg (EuclideanSpace.basisFun (Fin n) ℝ) (congrFun hσ k).symm
  rw [hv, hsym _ hj]

/-- Symmetry identifies a basis evaluation with the canonical multiindex
representative in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
private theorem symmetric_basis_eq_canonical {n m j : ℕ}
    (A : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℝ)
    (hsym : ∀ j ≤ m, ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
      ∀ σ : Equiv.Perm (Fin j), A j (v ∘ σ) = A j v)
    (hj : j ≤ m) (a : Fin j → Fin n) :
    ∃ α ∈ sobolevMultiindices n m,
      A j (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k)) =
        A (sobolevDerivativeList (fun i ↦ α (some i))).length
          (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ
            ((sobolevDerivativeList (fun i ↦ α (some i))).get k)) := by
  classical
  let β := fun i ↦ (List.ofFn a).count i
  let α : Option (Fin n) → ℕ := Option.elim' (m - j) β
  have hβ : ∑ i, β i = j := sum_counts a
  have hα : α ∈ sobolevMultiindices n m := by
    rw [mem_sobolevMultiindices]
    change m - j + ∑ i, β i = m
    rw [hβ, Nat.sub_add_cancel hj]
  refine ⟨α, hα, ?_⟩
  change A j (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k)) =
    A (sobolevDerivativeList β).length
      (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ ((sobolevDerivativeList β).get k))
  have hl : (sobolevDerivativeList β).length = j :=
    (sobolevDerivativeList_length β).trans hβ
  have hc : ∀ i, (sobolevDerivativeList β).count i = (List.ofFn a).count i :=
    sobolevDerivativeList_count β
  exact symmetric_basis_eq_list A hsym hj a (sobolevDerivativeList β) hl hc

/-- The finite-dimensional reverse jet bound for the derivative Sobolev norm
preceding `app:ch_regular_base:lem:ball-extension` and used in
`app:ch_regular_base:eq:ball-extension-sobolev`.

The constant is chosen before the family of jets and depends only on `n` and `m`.
The proof uses `1 + ∑ j ∈ Finset.range (m + 1), ((n : ℝ) ^ j) ^ 2`.
Only permutation symmetry through order `m` is needed. The canonical multiindex
sum counts each derivative once, and the result includes `n = 0`, `n = 1`, and
`m = 0`. -/
theorem exists_pos_symmetricJet_norm_sq_le_cartesian (n m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℝ,
        (∀ j ≤ m, ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
          ∀ σ : Equiv.Perm (Fin j), A j (v ∘ σ) = A j v) →
        (∑ j ∈ Finset.range (m + 1), ‖A j‖ ^ 2) ≤
          C * ∑ α ∈ sobolevMultiindices n m,
            (A (sobolevDerivativeList (fun i ↦ α (some i))).length
              (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ
                ((sobolevDerivativeList (fun i ↦ α (some i))).get k))) ^ 2 := by
  classical
  let C : ℝ := (∑ j ∈ Finset.range (m + 1), ((n : ℝ) ^ j) ^ 2) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A hsym
  let S : ℝ := ∑ α ∈ sobolevMultiindices n m,
    (A (sobolevDerivativeList (fun i ↦ α (some i))).length
      (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ
        ((sobolevDerivativeList (fun i ↦ α (some i))).get k))) ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hb (j : ℕ) (hj : j ≤ m) (a : Fin j → Fin n) :
      ‖A j (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))‖ ≤ Real.sqrt S := by
    obtain ⟨α, hα, he⟩ := symmetric_basis_eq_canonical A hsym hj a
    apply Real.le_sqrt_of_sq_le
    rw [he, Real.norm_eq_abs, sq_abs]
    dsimp [S]
    apply Finset.single_le_sum _ hα
    intro β _
    exact sq_nonneg _
  have hn (j : ℕ) (hj : j ≤ m) : ‖A j‖ ≤ (n : ℝ) ^ j * Real.sqrt S := by
    calc
      ‖A j‖ ≤ ∑ a : Fin j → Fin n,
          ‖A j (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ (a k))‖ := norm_le_basis_sum _
      _ ≤ ∑ _a : Fin j → Fin n, Real.sqrt S :=
        Finset.sum_le_sum (fun a _ ↦ hb j hj a)
      _ = _ := by simp
  have hsq (j : ℕ) (hj : j ≤ m) : ‖A j‖ ^ 2 ≤ ((n : ℝ) ^ j) ^ 2 * S := by
    calc
      ‖A j‖ ^ 2 ≤ ((n : ℝ) ^ j * Real.sqrt S) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hn j hj)
      _ = _ := by rw [mul_pow, Real.sq_sqrt hS]
  change (∑ j ∈ Finset.range (m + 1), ‖A j‖ ^ 2) ≤ C * S
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), ((n : ℝ) ^ j) ^ 2 * S :=
      Finset.sum_le_sum (fun j hj ↦ hsq j (by simpa using hj))
    _ = (∑ j ∈ Finset.range (m + 1), ((n : ℝ) ^ j) ^ 2) * S :=
      (Finset.sum_mul ..).symm
    _ ≤ C * S := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hS

end JanetCartan.BallExtension
