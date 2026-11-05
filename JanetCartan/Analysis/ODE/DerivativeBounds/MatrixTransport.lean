module

public import JanetCartan.Analysis.ODE.DerivativeBounds.Gronwall
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix transport and its inverse

The bounded-matrix-range step of `app:ch_regular_base:lem:buffered-interpolation`.
For given solutions of `U' = -CU` and `W' = WC` starting at the identity, we
prove that `W = U⁻¹`, and bound both matrices in the Frobenius norm. In particular
the identity's norm is retained; it is not replaced by the operator-norm value 1.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `app:ch_regular_base:lem:buffered-interpolation`: left matrix transport with
a bounded coefficient has a fixed-time Frobenius bound. -/
theorem norm_matrixTransport_le_exp
    {U C : ℝ → Matrix ι ι ℝ} {a b K : ℝ}
    (hK : 0 ≤ K) (hU : ContinuousOn U (Icc a b))
    (hU' : ∀ t ∈ Ico a b, HasDerivWithinAt U (-(C t * U t)) (Ici t) t)
    (hC : ∀ t ∈ Ico a b, ‖C t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖U t‖ ≤ ‖U a‖ * Real.exp (K * (b - a)) := by
  apply norm_le_exp_of_norm_deriv_le hK hU hU' _ ht
  intro τ hτ
  rw [norm_neg]
  exact (Matrix.frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (hC τ hτ) (norm_nonneg _))

/-- `app:ch_regular_base:lem:buffered-interpolation`: right matrix transport
obeys the same bound; this is the equation for the inverse fundamental matrix. -/
theorem norm_inverseMatrixTransport_le_exp
    {W C : ℝ → Matrix ι ι ℝ} {a b K : ℝ}
    (hK : 0 ≤ K) (hW : ContinuousOn W (Icc a b))
    (hW' : ∀ t ∈ Ico a b, HasDerivWithinAt W (W t * C t) (Ici t) t)
    (hC : ∀ t ∈ Ico a b, ‖C t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖W t‖ ≤ ‖W a‖ * Real.exp (K * (b - a)) := by
  apply norm_le_exp_of_norm_deriv_le hK hW hW' _ ht
  intro τ hτ
  calc
    ‖W τ * C τ‖ ≤ ‖W τ‖ * ‖C τ‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ ‖W τ‖ * K := mul_le_mul_of_nonneg_left (hC τ hτ) (norm_nonneg _)
    _ = K * ‖W τ‖ := mul_comm _ _

/-- `app:ch_regular_base:lem:buffered-interpolation`: the companion solution
`W' = WC` starting at the identity is the actual inverse of `U' = -CU`.
This follows by differentiating `WU`; inverse identification is a conclusion. -/
theorem matrixTransport_inverse_eq
    {U W C : ℝ → Matrix ι ι ℝ} {a b : ℝ}
    (hU : ContinuousOn U (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hU' : ∀ t ∈ Ico a b, HasDerivWithinAt U (-(C t * U t)) (Ici t) t)
    (hW' : ∀ t ∈ Ico a b, HasDerivWithinAt W (W t * C t) (Ici t) t)
    (hUa : U a = 1) (hWa : W a = 1)
    {t : ℝ} (ht : t ∈ Icc a b) : (U t)⁻¹ = W t := by
  have hprod : ∀ τ ∈ Ico a b,
      HasDerivWithinAt (fun σ ↦ W σ * U σ - 1) 0 (Ici τ) τ := by
    intro τ hτ
    convert! ((hW' τ hτ).mul (hU' τ hτ)).sub_const (1 : Matrix ι ι ℝ) using 1
    simp [mul_assoc]
  have hzero : W t * U t - 1 = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := 0)
      ((hW.mul hU).sub continuousOn_const) hprod (by simp [hUa, hWa])
      (by intros; simp) t ht
  exact Matrix.inv_eq_left_inv (sub_eq_zero.mp hzero)

/-- `app:ch_regular_base:lem:buffered-interpolation`: the fundamental matrix
and its actual inverse stay in a uniformly bounded Frobenius range. Only the
low bound on `C` enters the exponential, independently of higher derivatives. -/
theorem norm_matrixTransport_add_norm_inv_le
    {U W C : ℝ → Matrix ι ι ℝ} {a b K : ℝ}
    (hK : 0 ≤ K) (hU : ContinuousOn U (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hU' : ∀ t ∈ Ico a b, HasDerivWithinAt U (-(C t * U t)) (Ici t) t)
    (hW' : ∀ t ∈ Ico a b, HasDerivWithinAt W (W t * C t) (Ici t) t)
    (hUa : U a = 1) (hWa : W a = 1)
    (hC : ∀ t ∈ Ico a b, ‖C t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖U t‖ + ‖(U t)⁻¹‖ ≤ 2 * ‖(1 : Matrix ι ι ℝ)‖ * Real.exp (K * (b - a)) := by
  rw [matrixTransport_inverse_eq hU hW hU' hW' hUa hWa ht]
  have h₁ := norm_matrixTransport_le_exp hK hU hU' hC ht
  have h₂ := norm_inverseMatrixTransport_le_exp hK hW hW' hC ht
  rw [hUa] at h₁
  rw [hWa] at h₂
  calc
    _ ≤ ‖(1 : Matrix ι ι ℝ)‖ * Real.exp (K * (b - a)) +
        ‖(1 : Matrix ι ι ℝ)‖ * Real.exp (K * (b - a)) := add_le_add h₁ h₂
    _ = _ := by ring

end JanetCartan
