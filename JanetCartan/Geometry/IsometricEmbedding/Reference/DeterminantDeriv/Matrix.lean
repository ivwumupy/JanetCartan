module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The determinant differential

The adjugate formula used in Proposition `app:ch_seed:prop:seed-strata` of
`paper.tex`. The matrix space carries the Frobenius norm. The proof differentiates
the determinant as a multilinear function of its rows, so it applies to singular
matrices as well.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def determinantRows :
    ContinuousMultilinearMap ℝ (fun _ : ι ↦ ι → ℝ) ℝ where
  toMultilinearMap := detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

/-- Proposition app:ch_seed:prop:seed-strata: replacing a row contracts that
row with the corresponding column of the adjugate. -/
theorem det_updateRow_eq_sum_adjugate (A : Matrix ι ι ℝ) (b : ι → ℝ) (i : ι) :
    (A.updateRow i b).det = ∑ j, A.adjugate j i * b j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  rfl

open scoped Matrix.Norms.Frobenius

/-- Proposition app:ch_seed:prop:seed-strata: the determinant is differentiable,
including at singular matrices, with the Frobenius norm on matrices. -/
theorem differentiable_det : Differentiable ℝ (det : Matrix ι ι ℝ → ℝ) := by
  intro A
  exact (determinantRows.hasFDerivAt A).differentiableAt

/-- Proposition app:ch_seed:prop:seed-strata: Jacobi's formula without an
invertibility assumption, in the Frobenius matrix norm. -/
theorem fderiv_det_apply (A H : Matrix ι ι ℝ) :
    fderiv ℝ det A H = (A.adjugate * H).trace := by
  have hd : HasFDerivAt det (determinantRows.linearDeriv A) A :=
    determinantRows.hasFDerivAt A
  rw [hd.fderiv]
  calc
    _ = ∑ i, (A.updateRow i (H i)).det := determinantRows.linearDeriv_apply _ _
    _ = _ := by
      simp_rw [det_updateRow_eq_sum_adjugate]
      simp only [trace, diag_apply, mul_apply]
      exact Finset.sum_comm

end Matrix
