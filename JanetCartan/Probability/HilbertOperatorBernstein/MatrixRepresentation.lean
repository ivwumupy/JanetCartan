module

public import JanetCartan.Probability.OperatorBernstein
public import JanetCartan.Probability.OperatorCompression
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Orthonormal coordinates for operator Bernstein

The matrix realization used by `HilbertOperatorBernstein.operatorBernstein` in
`app:ch_waves:thm:sampling`. Matrix integrals use the Frobenius norm; the tail
uses the Euclidean operator norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.HilbertOperatorBernstein

variable {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E] [Fintype d] [DecidableEq d]

/-- Orthonormal matrix coordinates for the finite compressions in
`app:ch_waves:thm:sampling`. -/
def matrixEquiv (b : OrthonormalBasis d ℂ E) : (E →L[ℂ] E) ≃⋆ₐ[ℂ] Matrix d d ℂ :=
  b.repr.conjStarAlgEquiv.trans Matrix.toEuclideanCLM.symm

/-- The coordinate map is continuous for the Frobenius matrix topology
(`app:ch_waves:thm:sampling`, transfer of expectation and independence). -/
def matrixCLM (b : OrthonormalBasis d ℂ E) : (E →L[ℂ] E) →L[ℂ] Matrix d d ℂ :=
  (matrixEquiv b).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap

/-- Evaluation of the continuous coordinate map (`app:ch_waves:thm:sampling`). -/
@[simp] theorem matrixCLM_apply (b : OrthonormalBasis d ℂ E) (T : E →L[ℂ] E) :
    matrixCLM b T = matrixEquiv b T := rfl

omit [FiniteDimensional ℂ E] in
/-- The explicit Euclidean matrix norm is precisely the original operator norm
(`app:ch_waves:thm:sampling`). -/
@[simp] theorem operatorNorm_matrixEquiv (b : OrthonormalBasis d ℂ E)
    (T : E →L[ℂ] E) : OperatorBernstein.operatorNorm (matrixEquiv b T) = ‖T‖ := by
  simp only [OperatorBernstein.operatorNorm, matrixEquiv, StarAlgEquiv.trans_apply,
    StarAlgEquiv.apply_symm_apply]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using T.le_opNorm (b.repr.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (b.repr.conjStarAlgEquiv T).le_opNorm (b.repr x)
    simpa using h

omit [FiniteDimensional ℂ E] in
/-- Coordinates intertwine the operators and the basis isometry
(`app:ch_waves:thm:sampling`, variance transfer). -/
theorem toEuclideanCLM_matrixEquiv (b : OrthonormalBasis d ℂ E)
    (T : E →L[ℂ] E) :
    Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (matrixEquiv b T) = b.repr.conjStarAlgEquiv T := by
  simp [matrixEquiv]

omit [FiniteDimensional ℂ E] in
/-- Trace in orthonormal coordinates has no dimension normalization
(`app:ch_waves:thm:sampling`). -/
@[simp] theorem realTrace_matrixEquiv (b : OrthonormalBasis d ℂ E)
    (T : E →L[ℂ] E) :
    OperatorBernstein.realTrace (matrixEquiv b T) =
      (LinearMap.trace ℂ E T.toLinearMap).re := by
  have he (A : Matrix d d ℂ) :
      LinearMap.trace ℂ (EuclideanSpace ℂ d) (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) A).toLinearMap =
        A.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis]
    change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun d ℂ)
      ((LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun d ℂ)).symm A)).trace = _
    rw [StarAlgEquiv.apply_symm_apply]
  unfold OperatorBernstein.realTrace
  rw [← he, toEuclideanCLM_matrixEquiv]
  exact congrArg Complex.re (LinearMap.trace_conj' T.toLinearMap b.repr.toLinearEquiv)

end JanetCartan.HilbertOperatorBernstein
