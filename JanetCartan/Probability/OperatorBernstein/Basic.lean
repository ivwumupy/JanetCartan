module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite matrix conventions for operator Bernstein

Definitions for the concentration step of `app:ch_waves:thm:sampling` in `paper.tex`.
The ambient matrix norm remains Frobenius. The operator norm appearing in the
concentration event is explicitly the norm of the action on Euclidean space.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Euclidean operator norm used in `app:ch_waves:thm:sampling`. -/
def operatorNorm (A : Matrix d d ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) A‖

/-- The real trace, used on Hermitian matrices in `app:ch_waves:thm:sampling`. -/
def realTrace (A : Matrix d d ℂ) : ℝ := A.trace.re

/-- The variance `∑ q, E[Y_q²]` of the centered blocks in
`app:ch_waves:thm:sampling`. The integral uses the Frobenius norm. -/
def variance {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (Y : ι → Ω → Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ q, ∫ ω, Y q ω * Y q ω ∂μ

/-- The scalar function `φ` in Minsker (3.2), used in
`app:ch_waves:thm:sampling`. -/
def expRemainder (x : ℝ) : ℝ := Real.exp x - x - 1

/-- Nonnegativity of Minsker's `φ` (`app:ch_waves:thm:sampling`). -/
theorem expRemainder_nonneg (x : ℝ) : 0 ≤ expRemainder x := by
  unfold expRemainder
  linarith [Real.add_one_le_exp x]

/-- The Bernstein upper bound in `app:ch_waves:thm:sampling`, with an arbitrary
positive variance upper bound `v` and trace upper bound `τ`. -/
def tailBound (R v τ t : ℝ) : ℝ :=
  14 * τ / v * Real.exp (-(t ^ 2) / (2 * (v + R * t / 3)))

/-- The explicit operator norm is nonnegative (`app:ch_waves:thm:sampling`). -/
theorem operatorNorm_nonneg (A : Matrix d d ℂ) : 0 ≤ operatorNorm A :=
  norm_nonneg _

omit [DecidableEq d] in
/-- Positive semidefinite variance matrices have nonnegative real trace
(`app:ch_waves:thm:sampling`). -/
theorem realTrace_nonneg {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    0 ≤ realTrace A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

/-- Replacing the trace by an upper bound preserves the Bernstein bound
(`app:ch_waves:thm:sampling`). -/
theorem tailBound_mono_trace {R v τ τ' t : ℝ} (hv : 0 < v) (hτ : τ ≤ τ') :
    tailBound R v τ t ≤ tailBound R v τ' t := by
  unfold tailBound
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτ (by norm_num)) hv.le)
    (Real.exp_pos _).le

end JanetCartan.OperatorBernstein
