module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.Components

/-!
# Operator norm bounds through orthonormal components

The reverse comparison for `app:ch_regular_base:eq:ball-extension-sobolev`
uses scalar symmetric jets and a genuine operator norm inequality.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- Operator norms are bounded by the squared operator norms of output components,
not identified with them (`app:not:fourier`). -/
theorem norm_sq_le_sum_sq_components {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F)
    {j : ℕ} (A : E [×j]→L[ℝ] F) :
    ‖A‖ ^ 2 ≤ ∑ i, ‖(innerSL ℝ (b i)).compContinuousMultilinearMap A‖ ^ 2 := by
  let S := ∑ i, ‖(innerSL ℝ (b i)).compContinuousMultilinearMap A‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hb : ‖A‖ ≤ Real.sqrt S := by
    apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hS, ← b.sum_sq_inner_right (A v)]
    change _ ≤ S * (∏ k, ‖v k‖) ^ 2
    dsimp [S]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (((innerSL ℝ (b i)).compContinuousMultilinearMap A).le_opNorm v) 2
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      innerSL_apply_apply, Real.norm_eq_abs, sq_abs, mul_pow] using h
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (Real.sq_sqrt hS)

/-- The scalar symmetric-jet estimate extends to Hilbert outputs with the same
dimension-and-order constant (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem sum_sq_norm_symmetricJet_le {n : ℕ} [FiniteDimensional ℝ F] (m : ℕ)
    (A : (j : ℕ) → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (hsym : ∀ j ≤ m, ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
      ∀ σ : Equiv.Perm (Fin j), A j (v ∘ σ) = A j v) :
    (∑ j ∈ Finset.range (m + 1), ‖A j‖ ^ 2) ≤
      BallExtension.frechetEnergyComparisonConstant n m *
        ∑ α ∈ sobolevMultiindices n m,
          ‖A (sobolevDerivativeList (fun k ↦ α (some k))).length
            (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ
              ((sobolevDerivativeList (fun k ↦ α (some k))).get k))‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ F
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        ∑ i, ‖(innerSL ℝ (b i)).compContinuousMultilinearMap (A j)‖ ^ 2 :=
      Finset.sum_le_sum fun _ _ ↦ norm_sq_le_sum_sq_components b _
    _ = ∑ i, ∑ j ∈ Finset.range (m + 1),
        ‖(innerSL ℝ (b i)).compContinuousMultilinearMap (A j)‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ i, BallExtension.frechetEnergyComparisonConstant n m *
        ∑ α ∈ sobolevMultiindices n m,
          (inner ℝ (b i) (A (sobolevDerivativeList (fun k ↦ α (some k))).length
            (fun k ↦ EuclideanSpace.basisFun (Fin n) ℝ
              ((sobolevDerivativeList (fun k ↦ α (some k))).get k)))) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (BallExtension.exists_pos_symmetricJet_norm_sq_le_cartesian n m).choose_spec.2
        (fun j ↦ (innerSL ℝ (b i)).compContinuousMultilinearMap (A j))
      intro j hj v σ
      change inner ℝ (b i) (A j (v ∘ σ)) = inner ℝ (b i) (A j v)
      rw [hsym j hj]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [b.sum_sq_inner_right]

end JanetCartan.LocalSobolev
