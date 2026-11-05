module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PhysicalKernel
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakLimits

/-!
# Testing the physical first-order action

For `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`, this
is the integration-by-parts step needed to pass the frequency-regularized
solver identity to its strong L² limit. The zeroth-order coefficient is
retained. The scalar tests are real; their values against complex outputs
give both real and imaginary distributional identities.

The consumer is the uncut complete-residual construction. Its real matrix
coefficients are the physical pencil coefficients from `PhysicalKernel`.
Smooth coefficients and compact tests prove the formal test identity here;
no formal-adjoint or uncut residual equation is an input.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace JanetCartan.CharacteristicTransport.CompleteResidual

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "FV" => Fin q → ℂ

/-- The physical operator tested against one compact scalar test and one output
coordinate. Every coefficient derivative, including those of the test, is
retained (`app:ch_regular_base:eq:energy-complete-residual`). -/
def physicalTestAction (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ) (u : E → FV) (φ : E → ℝ) (i : Fin q) : ℂ :=
  -(∑ a, ∑ j, ∫ x, partialDeriv (fun y ↦ φ y * A y a i j) x a • u x j) +
    ∑ j, ∫ x, (φ x * B x i j) • u x j

private theorem partialDeriv_coordinate {u : E → FV} {x : E}
    (hu : DifferentiableAt ℝ u x) (a : Fin n) (j : Fin q) :
    partialDeriv u x a j = partialDeriv (fun y ↦ u y j) x a := by
  exact congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single a 1))
    (((ContinuousLinearMap.proj j).hasFDerivAt.comp x hu.hasFDerivAt).fderiv.symm)

/-- Integration by parts for the literal physical first-order matrix operator.
This applies to the smooth finite-frequency solver before taking any limit.
Compact support is required only of the test, not of the coefficients or
the solver (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem integral_firstOrderApply_eq_physicalTestAction
    (A : E → Fin n → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    {u : E → FV} (hu : ContDiff ℝ 1 u)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin q) :
    (∫ x, φ x • WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) u x i) =
      physicalTestAction A B u φ i := by
  have huj (j : Fin q) : ContDiff ℝ 1 (fun x ↦ u x j) :=
    (contDiff_pi.mp hu) j
  have hd (a : Fin n) (j : Fin q) : Continuous (fun x ↦ partialDeriv (fun y ↦ u y j) x a) :=
    ((huj j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hiA (a : Fin n) (j : Fin q) : Integrable
      (fun x ↦ (φ x * A x a i j) • partialDeriv (fun y ↦ u y j) x a) :=
    (((hφ.mul (hA a i j)).continuous).smul (hd a j)).integrable_of_hasCompactSupport
      (hc.mul_right.smul_right)
  have hiB (j : Fin q) : Integrable (fun x ↦ (φ x * B x i j) • u x j) :=
    (((hφ.mul (hB i j)).continuous).smul (huj j).continuous).integrable_of_hasCompactSupport
      (hc.mul_right.smul_right)
  have hparts (a : Fin n) (j : Fin q) :
      (∫ x, (φ x * A x a i j) • partialDeriv (fun y ↦ u y j) x a) =
        -(∫ x, partialDeriv (fun y ↦ φ y * A y a i j) x a • u x j) :=
    (Mollification.hasWeakFDerivOn_of_contDiff volume (huj j) univ).2.2
      _ (hφ.mul (hA a i j)) hc.mul_right (subset_univ _) (EuclideanSpace.single a 1)
  have hexp (x : E) : φ x • WKB.firstOrderApply
      (fun x a ↦ ((A x a).map Complex.ofReal).mulVecLin)
      (fun x ↦ ((B x).map Complex.ofReal).mulVecLin) u x i =
      (∑ a, ∑ j, (φ x * A x a i j) • partialDeriv (fun y ↦ u y j) x a) +
        ∑ j, (φ x * B x i j) • u x j := by
    simp only [WKB.firstOrderApply, Pi.add_apply, Finset.sum_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      smul_add, Finset.smul_sum, partialDeriv_coordinate (hu.differentiable one_ne_zero x)]
    simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  simp_rw [hexp]
  rw [integral_add (integrable_finsetSum _ (fun a _ ↦
      integrable_finsetSum _ (fun j _ ↦ hiA a j)))
    (integrable_finsetSum _ (fun j _ ↦ hiB j)),
    integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦ hiA a j)),
    integral_finsetSum _ (fun j _ ↦ hiB j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hiA _ j), hparts]
  simp only [physicalTestAction, Finset.sum_neg_distrib]

end JanetCartan.CharacteristicTransport.CompleteResidual
