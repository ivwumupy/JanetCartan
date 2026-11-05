module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Action.Integral
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.DifferentialFactors.FormalAdjoint

/-! # Source integration by parts for the image remainder

The source factor in `app:ch_background:prop:bg-frame`, Step 1, follows from
the divergence-form adjoint, with every coefficient retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I J : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Source integration by parts in the literal remainder composite
(`app:ch_background:prop:bg-frame`, Step 1). No adjoint identity is assumed. -/
theorem integral_kernel_coefficientFormalAdjoint
    (K : E × E → ℝ) (A : E → Fin d → Matrix I J ℝ) (Z : E → Matrix I J ℝ)
    (v : E → I → ℂ) (hK : ContDiff ℝ ∞ K)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hv : ∀ i, ContDiff ℝ ∞ (fun x ↦ v x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ v x i)) (x : E) (j : J) :
    (∫ y, (K (x,y) : ℂ) * coefficientFormalAdjoint A Z v y j) =
      ∑ k, ∫ y, (imageNormalSourceKernel K A Z j k (x,y) : ℂ) * v y k := by
  have hf : ContDiff ℝ ∞ (fun y ↦ (K (x,y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hK.comp (contDiff_const.prodMk contDiff_id))
  rw [integral_coefficientFormalAdjoint_column A Z _ v hA hZ hf hv hc j]
  have he (y : E) (k : I) :
      ((∑ a, (A y a k j : ℂ) * partialDeriv (fun z ↦ (K (x,z) : ℂ)) y a) +
        (Z y k j : ℂ) * (K (x,y) : ℂ)) =
      (imageNormalSourceKernel K A Z j k (x,y) : ℂ) := by
    simp only [imageNormalSourceKernel, Complex.ofReal_add, Complex.ofReal_sum,
      Complex.ofReal_mul, partialDeriv_imageNormal_kernel_source K hK]
  simp_rw [he]
  apply integral_finsetSum
  intro k _
  exact (((Complex.ofRealCLM.contDiff.comp
    (contDiff_imageNormalSourceKernel K A Z hK hA hZ j k)).comp
      (contDiff_const.prodMk contDiff_id)).continuous.mul (hv k).continuous).integrable_of_hasCompactSupport (hc k).mul_left

end JanetCartan.ContinuumNormalReduction.ImageNormal
