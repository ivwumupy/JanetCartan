module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.SingleMgf.Scalar
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Elementary matrix exponential and logarithm inequalities

Order inequalities for Minsker (3.3), used by `app:ch_waves:thm:sampling`.
The scalar inequalities are transported by the continuous functional calculus.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The tangent-line lower bound for the exponential of a Hermitian matrix,
used for positivity in Minsker (3.3) (`app:ch_waves:thm:sampling`). -/
theorem one_add_le_exp {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    1 + A ≤ NormedSpace.exp A := by
  have hsa : IsSelfAdjoint A := hA
  rw [← CFC.real_exp_eq_normedSpace_exp hsa]
  have h := (cfc_le_iff (fun x : ℝ => 1 + x) Real.exp A).2
    (fun x _ => by linarith [Real.add_one_le_exp x])
  rw [cfc_const_add 1 (fun x : ℝ => x) A (ha := hsa), cfc_id' ℝ A hsa, map_one] at h
  exact h

/-- The tangent-line upper bound for the logarithm of a positive definite matrix,
used in Minsker (3.3) (`app:ch_waves:thm:sampling`). -/
theorem log_le_sub_one {A : Matrix d d ℂ} (hA : A.PosDef) :
    CFC.log A ≤ A - 1 := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hc : ContinuousOn Real.log (spectrum ℝ A) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hA.isStrictlyPositive.spectrum_pos hx)
  have h := (cfc_le_iff Real.log (fun x : ℝ => x - 1) A hc).2
    (fun x hx => Real.log_le_sub_one_of_pos (hA.isStrictlyPositive.spectrum_pos hx))
  rw [cfc_sub (fun x : ℝ => x) (fun _ => 1) A, cfc_id' ℝ A hsa, cfc_const_one ℝ A hsa] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- A matrix above the identity is positive definite, as needed for the logarithm
in Minsker (3.3) (`app:ch_waves:thm:sampling`). -/
theorem posDef_of_one_le {A : Matrix d d ℂ} (hA : 1 ≤ A) : A.PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.of_le (a := (1 : Matrix d d ℂ)) isStrictlyPositive_one hA)

open scoped Matrix.Norms.L2Operator in
/-- The bounded Hermitian exponential estimate in Minsker Appendix A, before taking
expectations (`app:ch_waves:thm:sampling`). The bound uses the Euclidean operator norm. -/
theorem exp_smul_le_quadratic {A : Matrix d d ℂ} (hA : A.IsHermitian)
    {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hbound : operatorNorm A ≤ R) :
    NormedSpace.exp (θ • A) ≤
      1 + θ • A + (expRemainder (θ * R) / R ^ 2) • (A * A) := by
  cases isEmpty_or_nonempty d with
  | inl hd => exact le_of_eq (Subsingleton.elim _ _)
  | inr hd =>
    have hsa : IsSelfAdjoint A := hA
    have hθsa : IsSelfAdjoint θ := isSelfAdjoint_iff.mpr (star_trivial θ)
    let c := expRemainder (θ * R) / R ^ 2
    have h := (cfc_le_iff (fun x : ℝ => Real.exp (θ * x))
      (fun x : ℝ => 1 + θ * x + c * x ^ 2) A).2 (fun x hx => by
        apply exp_le_quadratic_of_abs_le hR hθ
        exact (spectrum.norm_le_norm_of_mem hx).trans hbound)
    have he : cfc (fun x : ℝ => Real.exp (θ * x)) A = NormedSpace.exp (θ • A) := by
      change cfc (Real.exp ∘ (fun x : ℝ => θ • x)) A = _
      rw [cfc_comp Real.exp (fun x : ℝ => θ • x) A hsa,
        cfc_smul_id θ A hsa, CFC.real_exp_eq_normedSpace_exp (hθsa.smul hsa)]
    have hq : cfc (fun x : ℝ => 1 + θ * x + c * x ^ 2) A =
        1 + θ • A + c • (A * A) := by
      rw [cfc_add A (fun x : ℝ => 1 + θ * x) (fun x : ℝ => c * x ^ 2),
        cfc_const_add 1 (fun x : ℝ => θ * x) A (ha := hsa), map_one]
      change 1 + cfc (fun x : ℝ => θ • x) A +
        cfc (fun x : ℝ => c • x ^ 2) A = _
      rw [cfc_smul_id θ A hsa, cfc_smul c (fun x : ℝ => x ^ 2) A,
        cfc_pow_id (R := ℝ) A 2 hsa, pow_two]
    rw [he, hq] at h
    exact h

end JanetCartan.OperatorBernstein
