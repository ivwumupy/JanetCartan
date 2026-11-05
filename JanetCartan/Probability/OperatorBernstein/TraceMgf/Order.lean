module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity

/-!
# Trace monotonicity for the independent-sum MGF bound

These deterministic inequalities support Minsker (3.4), used in
`app:ch_waves:thm:sampling` of `paper.tex`. Matrix order is the positive
semidefinite order; the ambient norm remains Frobenius.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The trace pairing of positive semidefinite matrices is nonnegative
(`app:ch_waves:thm:sampling`, Minsker (3.4)). The product need not be Hermitian. -/
theorem realTrace_mul_nonneg {A B : Matrix d d ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ realTrace (A * B) := by
  have h := LiebConcavity.Klein.realTrace_mul_cfc_eq_sum hA.1 hB.1 id
  rw [cfc_id ℝ B hB.1.isSelfAdjoint] at h
  rw [h]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j))
      (Complex.normSq_nonneg _)

/-- Trace exponential is monotone on Hermitian matrices in the positive
semidefinite order (`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem realTrace_exp_mono {A B : Matrix d d ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) :
    realTrace (NormedSpace.exp A) ≤ realTrace (NormedSpace.exp B) := by
  have h := LiebConcavity.realTrace_sub_le_relativeEntropy
    (LiebConcavity.posDef_exp hA) (LiebConcavity.posDef_exp hB)
  have hp := realTrace_mul_nonneg (LiebConcavity.posDef_exp hA).posSemidef
    (Matrix.le_iff.mp hAB)
  rw [LiebConcavity.relativeEntropy, CFC.log_exp A hA.isSelfAdjoint,
    CFC.log_exp B hB.isSelfAdjoint] at h
  simp only [mul_sub, realTrace, Matrix.trace_sub, Complex.sub_re] at h hp ⊢
  linarith

end JanetCartan.OperatorBernstein
