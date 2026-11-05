module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.Kernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral

/-!
# Differentiation of the compact remainder integral

The output differentiation needed for `app:ch_background:prop:bg-frame`, Step 1.
All integral-interchange hypotheses follow from smoothness and compact support.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source partial of the real kernel after complexification, used in the
source integration by parts of `app:ch_background:prop:bg-frame`, Step 1. -/
theorem partialDeriv_imageNormal_kernel_source (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (x y : E) (a : Fin d) :
    partialDeriv (fun z ↦ (K (x,z) : ℂ)) y a =
      (fderiv ℝ K (x,y) (0, EuclideanSpace.single a 1) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp y
    ((hK.differentiable (by simp) (x,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)))
  change HasFDerivAt (fun z ↦ (K (x,z) : ℂ)) _ y at hd
  rw [partialDeriv, hd.fderiv]
  simp

private theorem partialDeriv_kernel_test (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (w : E → ℂ) (x y : E) (a : Fin d) :
    partialDeriv (fun z ↦ (K (z,y) : ℂ) * w y) x a =
      (fderiv ℝ K (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * w y := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x
    ((hK.differentiable (by simp) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)))).mul_const (w y)
  change HasFDerivAt (fun z ↦ (K (z,y) : ℂ) * w y) _ x at hd
  rw [partialDeriv, hd.fderiv]
  simp [mul_comm]

private theorem kernel_test_carrier (K : E × E → ℝ) (w : E → ℂ)
    (x y : E) (hy : y ∉ Prod.snd '' tsupport K) :
    (K (x,y) : ℂ) * w y = 0 := by
  have hp : (x,y) ∉ tsupport K := fun hp ↦ hy ⟨(x,y), hp, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport hp]

/-- Differentiability of a compact smooth kernel applied to a smooth test.
This supplies the finite-sum differentiation in the literal `P R P*` identity
of `app:ch_background:prop:bg-frame`, Step 1. -/
theorem differentiableAt_imageNormal_kernel_integral (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (w : E → ℂ) (hw : ContDiff ℝ ∞ w) (x : E) :
    DifferentiableAt ℝ (fun z ↦ ∫ y, (K (z,y) : ℂ) * w y) x := by
  have hf : ContDiff ℝ ∞ (fun p : E × E ↦ (K p : ℂ) * w p.2) :=
    (Complex.ofRealCLM.contDiff.comp hK).mul (hw.comp contDiff_snd)
  exact (FourierIntegral.GraphDifferentiation.hasFDerivAt_integral
    isOpen_univ (hKc.image continuous_snd) hf.contDiffOn
    (fun z _ y hy ↦ kernel_test_carrier K w z y hy) (mem_univ x)).differentiableAt

/-- Output differentiation passes under the literal compact-kernel integral;
its derivative is the joint kernel derivative in `(eₐ,0)`. This is the analytic
output step of `app:ch_background:prop:bg-frame`, Step 1. -/
theorem partialDeriv_imageNormal_kernel_integral (K : E × E → ℝ)
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (w : E → ℂ) (hw : ContDiff ℝ ∞ w) (x : E) (a : Fin d) :
    partialDeriv (fun z ↦ ∫ y, (K (z,y) : ℂ) * w y) x a =
      ∫ y, (fderiv ℝ K (x,y) (EuclideanSpace.single a 1, 0) : ℂ) * w y := by
  have hf : ContDiff ℝ ∞ (fun p : E × E ↦ (K p : ℂ) * w p.2) :=
    (Complex.ofRealCLM.contDiff.comp hK).mul (hw.comp contDiff_snd)
  have hs : ∀ z ∈ (univ : Set E), ∀ y ∉ Prod.snd '' tsupport K,
      (K (z,y) : ℂ) * w y = 0 := fun z _ y hy ↦ kernel_test_carrier K w z y hy
  have hd := FourierIntegral.GraphDifferentiation.hasFDerivAt_integral (μ := volume)
    isOpen_univ (hKc.image continuous_snd) hf.contDiffOn hs (mem_univ x)
  have hdi := FourierIntegral.GraphDifferentiation.integrable_section
    (μ := volume) (hKc.image continuous_snd)
    (contDiffOn_parameterFDeriv isOpen_univ isOpen_univ hf.contDiffOn).continuousOn
    (fun z hz y hy ↦ FourierIntegral.GraphDifferentiation.fderiv_section_eq_zero
      (f := fun p : E × E ↦ (K p : ℂ) * w p.2) isOpen_univ hs hz hy) (mem_univ x)
  rw [partialDeriv, hd.fderiv, ContinuousLinearMap.integral_apply hdi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ partialDeriv_kernel_test K hK w x y a

end JanetCartan.ContinuumNormalReduction.ImageNormal
