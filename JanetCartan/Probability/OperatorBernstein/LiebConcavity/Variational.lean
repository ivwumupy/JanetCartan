module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Variational ingredients for Lieb trace concavity

These definitions and identities support the finite-dimensional Lieb theorem used in
`app:ch_waves:thm:sampling` of `paper.tex` (Minsker, arXiv:1112.5448v3, Fact 5).
The relative entropy is unnormalized: `D(X,A) = Re tr(X (log X - log A))`.

The variational value is `Re tr(X H) - D(X,A) + Re tr X`. Its value at
`X = exp(H + log A)` is exactly `Re tr exp(H + log A)`. The identities below
do not assert that this is an upper bound, or that relative entropy is jointly
convex; those are separate mathematical obligations.

The ambient matrix norm is Frobenius. The transparency option permits Lean to
identify its induced topology with the topology in the matrix functional calculus.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder

namespace JanetCartan.OperatorBernstein.LiebConcavity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Unnormalized matrix relative entropy for the variational proof of Minsker's
Fact 5, used in `app:ch_waves:thm:sampling`. -/
def relativeEntropy (X A : Matrix d d ℂ) : ℝ :=
  realTrace (X * (CFC.log X - CFC.log A))

/-- The variational expression for Lieb's trace functional, used in
`app:ch_waves:thm:sampling`. This definition contains no bound or convexity claim. -/
def variationalValue (H X A : Matrix d d ℂ) : ℝ :=
  realTrace (X * H) - relativeEntropy X A + realTrace X

omit [Fintype d] [DecidableEq d] in
/-- The positive-definite domain in Minsker's Fact 5 is convex
(`app:ch_waves:thm:sampling`). This also covers an empty matrix index type. -/
theorem convex_posDef : Convex ℝ {A : Matrix d d ℂ | A.PosDef} := by
  rw [convex_iff_forall_pos]
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

/-- The exponential of a Hermitian matrix is positive definite, as required for
the variational optimizer in `app:ch_waves:thm:sampling`. -/
theorem posDef_exp {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    (NormedSpace.exp H).PosDef := by
  exact (Matrix.nonneg_iff_posSemidef.mp hH.isSelfAdjoint.exp_nonneg).posDef_iff_isUnit.mpr
    (NormedSpace.isUnit_exp H)

/-- The candidate optimizer belongs to the positive-definite domain of relative
entropy (`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem posDef_exp_add_log {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (A : Matrix d d ℂ) : (NormedSpace.exp (H + CFC.log A)).PosDef :=
  posDef_exp (hH.add IsSelfAdjoint.log.isHermitian)

/-- Logarithm of the variational optimizer for Minsker's Fact 5
(`app:ch_waves:thm:sampling`). -/
theorem log_exp_add_log {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (A : Matrix d d ℂ) :
    CFC.log (NormedSpace.exp (H + CFC.log A)) = H + CFC.log A :=
  CFC.log_exp _ (hH.isSelfAdjoint.add IsSelfAdjoint.log)

/-- Relative entropy vanishes on the diagonal
(`app:ch_waves:thm:sampling`, variational proof of Minsker Fact 5). -/
@[simp] theorem relativeEntropy_self (A : Matrix d d ℂ) : relativeEntropy A A = 0 := by
  simp [relativeEntropy, realTrace]

/-- Rewriting the variational value as a relative entropy against the candidate
optimizer (`app:ch_waves:thm:sampling`). Klein's inequality will supply its upper bound. -/
theorem variationalValue_eq_trace_sub_relativeEntropy {H : Matrix d d ℂ}
    (hH : H.IsHermitian) (X A : Matrix d d ℂ) :
    variationalValue H X A =
      realTrace X - relativeEntropy X (NormedSpace.exp (H + CFC.log A)) := by
  simp only [variationalValue, relativeEntropy, log_exp_add_log hH, mul_sub, mul_add,
    realTrace, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
  ring

/-- The candidate optimizer attains the desired trace functional
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem variationalValue_exp_add_log {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (A : Matrix d d ℂ) :
    variationalValue H (NormedSpace.exp (H + CFC.log A)) A =
      realTrace (NormedSpace.exp (H + CFC.log A)) := by
  simp [variationalValue_eq_trace_sub_relativeEntropy hH]

/-- The Jensen difference of the variational value is the negative Jensen
difference of relative entropy (`app:ch_waves:thm:sampling`). This is an algebraic
identity, with no convexity assumption or conclusion. -/
theorem variationalValue_mix_sub_mix (H X Y A B : Matrix d d ℂ) (a b : ℝ) :
    variationalValue H (a • X + b • Y) (a • A + b • B) -
      (a * variationalValue H X A + b * variationalValue H Y B) =
    a * relativeEntropy X A + b * relativeEntropy Y B -
      relativeEntropy (a • X + b • Y) (a • A + b • B) := by
  simp only [variationalValue, add_mul, smul_mul_assoc, realTrace,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  ring

end JanetCartan.OperatorBernstein.LiebConcavity
