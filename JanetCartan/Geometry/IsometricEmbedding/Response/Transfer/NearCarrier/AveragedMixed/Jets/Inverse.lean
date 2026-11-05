module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Basic
public import JanetCartan.Analysis.Matrix.InverseBounds.Algebra

/-!
# Inverse norm conversion and finite jet constants

The inverse coefficient budget for `app:ch_response:eq:direct-envelope-profile`.
The operator inverse is exactly the nonsingular matrix inverse under the fixed
realization. In particular the matrix estimate retains the Frobenius norm.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

local instance averagedMixedInverseMatrixTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

private def mixedMatrixRingEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℝ ≃+*
    (Euclidean n →L[ℝ] Euclidean n) :=
  { (mixedMatrixOperatorEquiv n).toLinearEquiv.toAddEquiv with
    map_mul' := by
      intro A B
      ext v i
      change Matrix.toEuclideanLin (A * B) v i =
        Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) i
      simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      rw [Matrix.toLin_mul (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
      rfl }

/-- The operator inverse converts to the literal matrix inverse used in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem mixedMatrixOperatorEquiv_symm_inverse {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (mixedMatrixOperatorEquiv n).symm (Ring.inverse (mixedMatrixOperatorEquiv n A)) =
      A⁻¹ := by
  apply (mixedMatrixOperatorEquiv n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, Matrix.nonsing_inv_eq_ringInverse]
  exact (map_ringInverse (mixedMatrixRingEquiv n) A).symm

/-- A finite primitive budget for the inverse deduction in
`app:ch_response:eq:direct-envelope-profile`, independent of `L` and frequency. -/
def averagedMixedJetBudget (n r : ℕ) (C : ℕ → ℝ) : ℝ :=
  max 1 (‖(mixedMatrixOperatorEquiv n).toContinuousLinearMap‖ *
    ∑ j ∈ Finset.range (r + 1), |C j|)

/-- Explicit operator inverse jet constant for
`app:ch_response:eq:direct-envelope-profile`. -/
def averagedMixedInverseJetConstant (n r : ℕ) (C : ℕ → ℝ) (M : ℝ) : ℝ :=
  (r.factorial : ℝ) * ((r.factorial : ℝ) * max 1 (2 * M) ^ (r + 1)) *
    averagedMixedJetBudget n r C ^ r

/-- Each positive-order primitive operator coefficient fits in the power
budget used by the inversion formula (`app:ch_response:eq:direct-envelope-profile`). -/
theorem mixedMatrix_jet_coefficient_le_budget_pow (n : ℕ) {r i : ℕ} (C : ℕ → ℝ)
    (hi : 1 ≤ i) (hir : i ≤ r) :
    ‖(mixedMatrixOperatorEquiv n).toContinuousLinearMap‖ * C i ≤
      averagedMixedJetBudget n r C ^ i := by
  have hc : C i ≤ ∑ j ∈ Finset.range (r + 1), |C j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j))
      (Finset.mem_range.mpr (by omega)))
  calc
    _ ≤ averagedMixedJetBudget n r C :=
      (mul_le_mul_of_nonneg_left hc
        (norm_nonneg (mixedMatrixOperatorEquiv n).toContinuousLinearMap)).trans (le_max_right _ _)
    _ ≤ averagedMixedJetBudget n r C ^ i :=
      le_self_pow₀ (le_max_left _ _) (by omega)

end JanetCartan.ResponseTransfer
