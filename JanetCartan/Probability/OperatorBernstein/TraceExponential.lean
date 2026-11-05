module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The variance trace bound in operator Bernstein

The deterministic step (3.5) of Minsker, arXiv:1112.5448v3, used in
`app:ch_waves:thm:sampling` of `paper.tex`. The bound uses any positive upper
bound on the operator norm, so it also applies to the zero variance matrix.
These results do not assert a probabilistic concentration inequality.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder

namespace JanetCartan.OperatorBernstein

/-- The scalar chord estimate underlying Minsker (3.5), used in
`app:ch_waves:thm:sampling`. -/
theorem exp_mul_sub_one_le {x v a : ℝ} (hx : 0 ≤ x) (hxv : x ≤ v) (hv : 0 < v) :
    Real.exp (a * x) - 1 ≤ x / v * (Real.exp (a * v) - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (a * v))
    (show 0 ≤ 1 - x / v by rw [sub_nonneg]; exact (div_le_one hv).2 hxv)
    (div_nonneg hx hv.le) (show 1 - x / v + x / v = 1 by ring)
  have heq : (1 - x / v) * 0 + x / v * (a * v) = a * x := by field_simp; ring
  simp only [smul_eq_mul, heq, Real.exp_zero, mul_one] at h
  nlinarith

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Spectral trace formula for the functional calculus in the concentration step
of `app:ch_waves:thm:sampling`. -/
theorem realTrace_cfc {A : Matrix d d ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    realTrace (cfc f A) = ∑ i, f (hA.eigenvalues i) := by
  rw [realTrace, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

/-- The real trace is the sum of the real eigenvalues
(`app:ch_waves:thm:sampling`). -/
theorem realTrace_eq_sum_eigenvalues {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    realTrace A = ∑ i, hA.eigenvalues i := by
  rw [realTrace, hA.trace_eq_sum_eigenvalues]
  simp

open scoped Matrix.Norms.L2Operator in
/-- Each Hermitian eigenvalue is bounded above by the Euclidean operator norm
(`app:ch_waves:thm:sampling`). -/
theorem eigenvalue_le_operatorNorm {A : Matrix d d ℂ} (hA : A.IsHermitian) (i : d) :
    hA.eigenvalues i ≤ operatorNorm A := by
  let : Nonempty d := ⟨i⟩
  exact (le_abs_self _).trans (spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i))

set_option backward.isDefEq.respectTransparency false in
/-- The matrix exponential minus the identity is the scalar functional calculus
used in Minsker (3.5) (`app:ch_waves:thm:sampling`). -/
theorem cfc_exp_mul_sub_one {A : Matrix d d ℂ} (hA : A.IsHermitian) (a : ℝ) :
    cfc (fun x : ℝ ↦ Real.exp (a * x) - 1) A = NormedSpace.exp (a • A) - 1 := by
  rw [cfc_sub _ _ A, cfc_const_one ℝ A hA.isSelfAdjoint]
  have heq : cfc (fun x : ℝ ↦ Real.exp (a * x)) A = cfc Real.exp (a • A) := by
    have h := cfc_comp Real.exp (fun x : ℝ ↦ a • x) A hA.isSelfAdjoint
    rw [cfc_smul_id a A hA.isSelfAdjoint] at h
    exact h
  rw [heq, CFC.real_exp_eq_normedSpace_exp (hA.smul (IsSelfAdjoint.all a)).isSelfAdjoint]

/-- Minsker (3.5) with an arbitrary positive variance upper bound, including zero
variance, as required by `app:ch_waves:thm:sampling`. -/
theorem realTrace_exp_sub_one_le {V : Matrix d d ℂ} (hV : V.PosSemidef)
    {v : ℝ} (hv : 0 < v) (hVv : operatorNorm V ≤ v) (a : ℝ) :
    realTrace (NormedSpace.exp (a • V) - 1) ≤
      realTrace V / v * (Real.exp (a * v) - 1) := by
  rw [← cfc_exp_mul_sub_one hV.isHermitian a, realTrace_cfc hV.isHermitian,
    realTrace_eq_sum_eigenvalues hV.isHermitian, Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ exp_mul_sub_one_le (hV.eigenvalues_nonneg i)
    ((eigenvalue_le_operatorNorm hV.isHermitian i).trans hVv) hv

/-- The slightly weaker form of Minsker (3.5) used in (3.6), with the trace
prefactor of `app:ch_waves:thm:sampling`. -/
theorem realTrace_exp_sub_one_le_exp {V : Matrix d d ℂ} (hV : V.PosSemidef)
    {v : ℝ} (hv : 0 < v) (hVv : operatorNorm V ≤ v) (a : ℝ) :
    realTrace (NormedSpace.exp (a • V) - 1) ≤
      realTrace V / v * Real.exp (a * v) := by
  refine (realTrace_exp_sub_one_le hV hv hVv a).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (realTrace_nonneg hV) hv.le)

end JanetCartan.OperatorBernstein
