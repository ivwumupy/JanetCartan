module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Action.Source

/-!
# The literal two-factor image remainder action

The identity `P R P*` in `app:ch_background:prop:bg-frame`, Step 1, for a
compact smooth kernel. Source integration by parts and output differentiation
under the integral produce exactly `imageNormalTwoFactorKernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Literal identification of `P R P*` with the differentiated remainder
kernel in `app:ch_background:prop:bg-frame`, Step 1. Both first-order factors
and both zeroth-order coefficients are retained. The compact smooth test
assumptions imply every integration-by-parts and differentiation hypothesis. -/
theorem coefficientOperator_integral_coefficientFormalAdjoint
    (K : E × E → ℝ) (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x : E) (i : I) :
    coefficientOperator A Z
      (fun z j ↦ ∫ y, (K (z,y) : ℂ) * coefficientFormalAdjoint A Z v y j) x i =
      ∑ k, ∫ y, (imageNormalTwoFactorKernel K A Z i k (x,y) : ℂ) * v y k := by
  let S := imageNormalSourceKernel K A Z
  have hS (j : J) (k : I) : ContDiff ℝ ∞ (S j k) :=
    contDiff_imageNormalSourceKernel K A Z hK hA hZ j k
  have hSc (j : J) (k : I) : HasCompactSupport (S j k) :=
    hasCompactSupport_imageNormalSourceKernel K A Z hKc j k
  have he : (fun z j ↦ ∫ y, (K (z,y) : ℂ) * coefficientFormalAdjoint A Z v y j) =
      fun z j ↦ ∑ k, ∫ y, (S j k (z,y) : ℂ) * v y k := by
    funext z j
    exact integral_kernel_coefficientFormalAdjoint K A Z v hK hA hZ hv hc z j
  have hd (j : J) (a : Fin d) :
      partialDeriv (fun z ↦ ∑ k, ∫ y, (S j k (z,y) : ℂ) * v y k) x a =
        ∑ k, ∫ y, (fderiv ℝ (S j k) (x,y) (EuclideanSpace.single a 1, 0) : ℂ) *
          v y k := by
    have hdif (k : I) : DifferentiableAt ℝ
        (fun z ↦ ∫ y, (S j k (z,y) : ℂ) * v y k) x :=
      differentiableAt_imageNormal_kernel_integral (S j k) (hS j k) (hSc j k)
        (fun y ↦ v y k) (hv k) x
    rw [partialDeriv, fderiv_fun_sum (fun k _ ↦ hdif k)]
    simp only [sum_apply]
    exact Finset.sum_congr rfl fun k _ ↦
      partialDeriv_imageNormal_kernel_integral (S j k) (hS j k) (hSc j k)
        (fun y ↦ v y k) (hv k) x a
  have hV (j : J) (k : I) : Integrable (fun y ↦ (S j k (x,y) : ℂ) * v y k) :=
    (((Complex.ofRealCLM.contDiff.comp (hS j k)).comp
      (contDiff_const.prodMk contDiff_id)).continuous.mul (hv k).continuous).integrable_of_hasCompactSupport (hc k).mul_left
  have hD (a : Fin d) (j : J) (k : I) : Integrable (fun y ↦
      (fderiv ℝ (S j k) (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * v y k) := by
    have hdS : ContDiff ℝ ∞ (fun p : E × E ↦
        fderiv ℝ (S j k) p (EuclideanSpace.single a 1, 0)) :=
      ((hS j k).fderiv_right (by simp)).clm_apply contDiff_const
    exact (((Complex.ofRealCLM.contDiff.comp hdS).comp
      (contDiff_const.prodMk contDiff_id)).continuous.mul (hv k).continuous).integrable_of_hasCompactSupport (hc k).mul_left
  have hT (a : Fin d) (j : J) (k : I) : Integrable (fun y ↦ (A x a i j : ℂ) *
      (fderiv ℝ (S j k) (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * v y k) := by
    simpa only [mul_assoc] using (hD a j k).const_mul (A x a i j : ℂ)
  have hW (j : J) (k : I) : Integrable (fun y ↦
      (Z x i j : ℂ) * (S j k (x,y) : ℂ) * v y k) := by
    simpa only [mul_assoc] using (hV j k).const_mul (Z x i j : ℂ)
  have hk (k : I) :
      (∫ y, (imageNormalTwoFactorKernel K A Z i k (x,y) : ℂ) * v y k) =
      (∑ a, ∑ j, (A x a i j : ℂ) *
        ∫ y, (fderiv ℝ (S j k) (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * v y k) +
      ∑ j, (Z x i j : ℂ) * ∫ y, (S j k (x,y) : ℂ) * v y k := by
    simp only [imageNormalTwoFactorKernel, Complex.ofReal_add, Complex.ofReal_sum,
      Complex.ofReal_mul, add_mul, Finset.sum_mul]
    change (∫ y, (∑ a, ∑ j, (A x a i j : ℂ) *
      (fderiv ℝ (S j k) (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * v y k) +
      ∑ j, (Z x i j : ℂ) * (S j k (x,y) : ℂ) * v y k) = _
    rw [integral_add
      (integrable_finsetSum Finset.univ fun a _ ↦
        integrable_finsetSum Finset.univ fun j _ ↦ hT a j k)
      (integrable_finsetSum Finset.univ fun j _ ↦ hW j k)]
    rw [integral_finsetSum Finset.univ (fun a _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ hT a j k),
      integral_finsetSum Finset.univ (fun j _ ↦ hW j k)]
    simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hT _ j k),
      mul_assoc, integral_const_mul]
  rw [he]
  simp only [coefficientOperator, hd, Finset.mul_sum, hk, Finset.sum_add_distrib]
  congr 1
  · conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

end JanetCartan.ContinuumNormalReduction.ImageNormal
