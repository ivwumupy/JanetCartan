module

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Integral representatives of the L² Fourier transform

The compatibility needed for the compact regularization in
`app:ch_osc:lem:osc-amplitude`, deduced from the tempered-distribution transform.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff

namespace JanetCartan.AmplitudeBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The L² Fourier transform of an integrable representative is the Fourier integral
almost everywhere (`app:ch_osc:lem:osc-amplitude`). -/
theorem fourierTransform_coeFn_ae_integral (f : Lp (α := E) ℂ 2)
    (hf : Integrable (f : E → ℂ)) :
    (𝓕 f : Lp (α := E) ℂ 2) =ᵐ[volume] 𝓕 (f : E → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution E ℂ ↦ T s)
    (Lp.fourier_toTemperedDistribution_eq f)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner s.integrable hf
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  have hs' : (∫ x, (𝓕 s) x * f x) = ∫ x, s x * 𝓕 (f : E → ℂ) x := by
    simpa using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

/-- The inverse L² Fourier transform of an integrable representative is the inverse
Fourier integral almost everywhere (`app:ch_osc:lem:osc-amplitude`). -/
theorem fourierTransformInv_coeFn_ae_integral (f : Lp (α := E) ℂ 2)
    (hf : Integrable (f : E → ℂ)) :
    (𝓕⁻ f : Lp (α := E) ℂ 2) =ᵐ[volume] 𝓕⁻ (f : E → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ f)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hf).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution E ℂ ↦ T s)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume) (L := -innerₗ E)
    Real.continuous_fourierChar continuous_inner.neg s.integrable hf
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  have hs' : (∫ x, (𝓕⁻ s) x * f x) = ∫ x, s x * 𝓕⁻ (f : E → ℂ) x := by
    have hcoe (x : E) : (𝓕⁻ s) x = 𝓕⁻ (s : E → ℂ) x :=
      congrFun (SchwartzMap.fourierInv_coe s) x
    simp_rw [hcoe]
    simpa [FourierTransformInv.fourierInv,
      VectorFourier.fourierIntegral, real_inner_comm] using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

end JanetCartan.AmplitudeBound
