module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Coordinate budgets and Fréchet derivative norms

The finite-dimensional norm comparisons used in Step 3 of
`app:ch_regular_base:thm:actual-calculus` and
`app:lem:elementary-interpolation-jets` of `paper.tex`.
-/

@[expose] public noncomputable section

open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

/-- `app:lem:elementary-interpolation-jets`: ordered physical derivatives are
Fréchet derivatives evaluated on the corresponding ordered coordinate vectors. -/
theorem euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv {n k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (a : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanCoordinateDerivList (List.ofFn a) f x =
      iteratedFDeriv ℝ k f x (fun i ↦ EuclideanSpace.single (a i) 1) := by
  induction k generalizing x with
  | zero => simp [euclideanCoordinateDerivList, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ, euclideanCoordinateDerivList]
    rw [show euclideanCoordinateDerivList (List.ofFn (fun i ↦ a i.succ)) f =
      (fun y ↦ iteratedFDeriv ℝ k f y (fun i ↦ EuclideanSpace.single (a i.succ) 1)) from
        funext (fun y ↦ ih _ y)]
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left']
    · rfl
    · exact (ContDiff.differentiable_iteratedFDeriv (n := ∞) (m := k) (by exact_mod_cast ENat.natCast_lt_top k) hf).differentiableAt

/-- `app:lem:elementary-interpolation-jets`: coordinate evaluations are bounded
by the Fréchet operator norm, with constant one. -/
theorem norm_euclideanCoordinateDerivList_le_iteratedFDeriv {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (is : List (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanCoordinateDerivList is f x‖ ≤ ‖iteratedFDeriv ℝ is.length f x‖ := by
  have h := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hf is.get x
  rw [List.ofFn_get] at h
  rw [h]
  simpa [EuclideanSpace.single, PiLp.norm_single] using
    (iteratedFDeriv ℝ is.length f x).le_opNorm (fun i ↦ EuclideanSpace.single (is.get i) 1)

/-- `app:lem:elementary-interpolation-jets`: expansion in the standard basis
bounds a complex-valued multilinear map by its coordinate evaluations. -/
theorem norm_complexMultilinear_le_coordinate_sum {n k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) ℂ) :
    ‖A‖ ≤ ∑ a : Fin k → Fin n, ‖A (fun i ↦ EuclideanSpace.single (a i) 1)‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  simp only [← EuclideanSpace.basisFun_apply]
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv : v = fun i ↦ ∑ j, b.repr (v i) j • b j := by
    funext i
    exact (b.sum_repr (v i)).symm
  calc
    ‖A v‖ = ‖∑ a : Fin k → Fin n, (∏ i, b.repr (v i) (a i)) •
        A (fun i ↦ b (a i))‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin k → Fin n, ‖(∏ i, b.repr (v i) (a i)) •
        A (fun i ↦ b (a i))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin k → Fin n, ‖A (fun i ↦ b (a i))‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro i _
      exact (PiLp.norm_apply_le (b.repr (v i)) (a i)).trans_eq (b.repr.norm_map _)
    _ = _ := (Finset.sum_mul ..).symm

/-- `app:ch_regular_base:thm:actual-calculus`, Step 3: a physical coordinate
budget gives explicit finite Fréchet bounds, without any support assumption. -/
theorem norm_iteratedFDeriv_le_amplitudeBudget {X : Type*} {n N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ))
    {A : ℝ} (hA : HasAmplitudeDerivativeBound b N A)
    (ξ : X) {k : ℕ} (hk : k ≤ N) (z : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (b ξ) z‖ ≤ (n : ℝ) ^ k * A := by
  apply (norm_complexMultilinear_le_coordinate_sum _).trans
  calc
    _ ≤ ∑ _a : Fin k → Fin n, A := by
      apply Finset.sum_le_sum
      intro a _
      rw [← euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv (hb ξ)]
      exact hA ξ _ (by simpa using hk) z
    _ = _ := by simp

/-- `app:lem:elementary-interpolation-jets`: the comparison constant for the
sum of Fréchet derivative suprema through order `N`. -/
def physicalBudgetCNormConstant (n N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), (n : ℝ) ^ k

/-- `app:lem:elementary-interpolation-jets`: this comparison constant is positive,
including in dimension zero. -/
theorem physicalBudgetCNormConstant_pos (n N : ℕ) :
    0 < physicalBudgetCNormConstant n N := by
  have h : (1 : ℝ) ≤ physicalBudgetCNormConstant n N := by
    simpa [physicalBudgetCNormConstant] using
      (Finset.single_le_sum (f := fun k ↦ (n : ℝ) ^ k)
        (s := Finset.range (N + 1)) (fun _ _ ↦ by positivity)
        (show 0 ∈ Finset.range (N + 1) by simp))
  linarith

/-- `app:lem:elementary-interpolation-jets`: coordinate budgets bound the
existing `cNorm` on every set, in particular a fixed ball containing the support. -/
theorem cNorm_le_amplitudeBudget {X : Type*} {n N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ))
    {A : ℝ} (hA : HasAmplitudeDerivativeBound b N A)
    (ξ : X) (s : Set (EuclideanSpace ℝ (Fin n))) :
    cNorm s N (b ξ) ≤ physicalBudgetCNormConstant n N * A := by
  have hnonneg : 0 ≤ A := (norm_nonneg _).trans (hA.norm_le ξ 0)
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), (n : ℝ) ^ k * A :=
      cNorm_le_sum_of_bounds (fun _ _ ↦ by positivity)
        (fun k hk z _ ↦ norm_iteratedFDeriv_le_amplitudeBudget hb hA ξ hk z)
    _ = _ := by rw [physicalBudgetCNormConstant, Finset.sum_mul]

end JanetCartan.Pseudodifferential
