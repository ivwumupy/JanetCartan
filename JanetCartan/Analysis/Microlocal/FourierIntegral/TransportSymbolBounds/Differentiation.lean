module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Pointwise
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Actual spatial derivatives of the correction amplitude

The derivative in `app:ch_regular_base:eq:direct-graph-identity` acts on every
factor of both terms in `b₋₁`. Here `c1` and `c2` are the supplied covector jets
after evaluation at `(x,S_x)`; their spatial derivatives therefore include the
chain rule. The phase and coefficient owners must supply these evaluated jets.
No derivative bound for the correction or the remainder is an input.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace JanetCartan.FourierIntegral
variable {E ι R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [NormedRing R] [NormedAlgebra ℂ R]

local instance : NormedAlgebra ℝ R := NormedAlgebra.restrictScalars ℝ ℂ R

/-- All five differentiated products in
`app:ch_regular_base:eq:direct-graph-identity`, in their original order. -/
def correctionAmplitudeDifferential (c1 dU dc1 ddU : ι → R)
    (c2 dc2 : ι → ι → R) (S dS : ι → ι → ℂ) (U dV : R) : R :=
  -Complex.I • (∑ j, (dc1 j * dU j + c1 j * ddU j)) -
    (Complex.I / 2) • (∑ j, ∑ l,
      (dS j l • (c2 j l * U) + S j l • (dc2 j l * U + c2 j l * dV)))

/-- The formal five-term expression is the actual directional Fréchet
 derivative, as required by `app:ch_regular_base:eq:direct-graph-identity`. -/
theorem fderiv_correctionAmplitude_apply
    (c1 dU : ι → E → R) (c2 : ι → ι → E → R)
    (S : ι → ι → E → ℂ) (U : E → R) (x v : E)
    (hc1 : ∀ j, DifferentiableAt ℝ (c1 j) x)
    (hdU : ∀ j, DifferentiableAt ℝ (dU j) x)
    (hc2 : ∀ j l, DifferentiableAt ℝ (c2 j l) x)
    (hS : ∀ j l, DifferentiableAt ℝ (S j l) x)
    (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y ↦ correctionAmplitude (fun j ↦ c1 j y)
      (fun j ↦ dU j y) (fun j l ↦ c2 j l y) (fun j l ↦ S j l y) (U y)) x v =
      correctionAmplitudeDifferential (fun j ↦ c1 j x) (fun j ↦ dU j x)
        (fun j ↦ fderiv ℝ (c1 j) x v) (fun j ↦ fderiv ℝ (dU j) x v)
        (fun j l ↦ c2 j l x) (fun j l ↦ fderiv ℝ (c2 j l) x v)
        (fun j l ↦ S j l x) (fun j l ↦ fderiv ℝ (S j l) x v)
        (U x) (fderiv ℝ U x v) := by
  have hfirst := HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) ↦
    (hc1 j).hasFDerivAt.mul' (hdU j).hasFDerivAt)
  have hsecond := HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) ↦
    HasFDerivAt.fun_sum (fun l (_ : l ∈ Finset.univ) ↦
      (hS j l).hasFDerivAt.smul ((hc2 j l).hasFDerivAt.mul' hU.hasFDerivAt)))
  have h := (hfirst.const_smul (-Complex.I)).sub (hsecond.const_smul (Complex.I / 2))
  simpa only [correctionAmplitude, correctionAmplitudeDifferential, sub_apply,
    sum_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.mul_apply, Pi.smul_apply', Pi.smul_def, Pi.sub_def, add_comm] using
    congrArg (fun T : E →L[ℝ] R ↦ T v) h.fderiv

/-- A primitive-only bound on all five terms of the actual differentiated
correction (`app:ch_regular_base:eq:direct-graph-identity`). -/
theorem norm_correctionAmplitudeDifferential_le
    (c1 dU dc1 ddU : ι → R) (c2 dc2 : ι → ι → R)
    (S dS : ι → ι → ℂ) (U dV : R) :
    ‖correctionAmplitudeDifferential c1 dU dc1 ddU c2 dc2 S dS U dV‖ ≤
      (∑ j, (‖dc1 j‖ * ‖dU j‖ + ‖c1 j‖ * ‖ddU j‖)) +
        (1 / 2 : ℝ) * ∑ j, ∑ l,
          (‖dS j l‖ * (‖c2 j l‖ * ‖U‖) +
            ‖S j l‖ * (‖dc2 j l‖ * ‖U‖ + ‖c2 j l‖ * ‖dV‖)) := by
  unfold correctionAmplitudeDifferential
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, norm_neg, Complex.norm_I, norm_div, Complex.norm_ofNat,
    one_mul]
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun j _ ↦ (norm_add_le _ _).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l _
    apply (norm_add_le _ _).trans
    simp only [norm_smul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (norm_nonneg _))

end JanetCartan.FourierIntegral
