module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# Pointwise reconstruction of Euclidean envelopes

For the envelope jets from `app:ch_response:eq:response-graded-source`, a
continuous L² envelope is reconstructed from its integrable L² Fourier
representative. The hypothesis of Fourier integrability is produced by
`SobolevEnvelopeBounds.fourier_integrable` in `EnvelopeJets.Moments`.
This supplies the reconstruction step for the original-source estimate before
`app:ch_response:eq:response-graded-reduced`.

We identify the inverse integral with the L² inverse using tempered
distributions, as in the forward identification in
`Localization.fourierTransform_coeFn_ae_integral_hilbert`. Continuity then
upgrades almost-everywhere reconstruction to equality at every point. The
envelope itself need not be L¹, and all transforms use Mathlib's normalization.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff

namespace JanetCartan.ResponseTransfer.SourceNegative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The inverse L² transform agrees almost everywhere with the inverse integral.
This is the identification used by `eq_fourierInv_l2_of_continuous` to reconstruct
the envelope in `app:ch_response:eq:response-graded-source`. -/
private theorem fourierInv_coeFn_ae_integral (u : Lp (α := Euclidean n) F 2 volume)
    (hu : Integrable (u : Euclidean n → F)) :
    (𝓕⁻ u : Lp (α := Euclidean n) F 2 volume) =ᵐ[volume]
      𝓕⁻ (u : Euclidean n → F) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ u)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hu).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution (Euclidean n) F ↦ T s)
    (Lp.fourierInv_toTemperedDistribution_eq u)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ) (μ := volume) (ν := volume)
    (L := -innerₗ (Euclidean n))
    Real.continuous_fourierChar continuous_inner.neg s.integrable hu
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hd
  have hs' : (∫ x, (𝓕⁻ s) x • u x) = ∫ x, s x • 𝓕⁻ (u : Euclidean n → F) x := by
    have hcoe (x : Euclidean n) : (𝓕⁻ s) x = 𝓕⁻ (s : Euclidean n → ℂ) x :=
      congrFun (SchwartzMap.fourierInv_coe s) x
    simp_rw [hcoe]
    simpa [FourierTransformInv.fourierInv,
      VectorFourier.fourierIntegral, real_inner_comm] using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

/-- Reconstruct a continuous L² envelope from its integrable L² Fourier
representative, for the jets required by the original-source estimate before
`app:ch_response:eq:response-graded-reduced`. For the profile
`app:ch_response:eq:response-graded-source`, the parent supplies `hcont` from
`SobolevEnvelopeBounds.smooth` and `hg` from
`SobolevEnvelopeBounds.fourier_integrable`. No L¹ hypothesis on `f` is required. -/
theorem eq_fourierInv_l2_of_continuous {f : Euclidean n → F}
    (hcont : Continuous f) (hf : MemLp f 2 volume)
    (hg : Integrable (fun ξ ↦ (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ)
      volume) :
    f = 𝓕⁻ (fun ξ ↦ (𝓕 (hf.toLp f) : Lp (α := Euclidean n) F 2 volume) ξ) := by
  have he := fourierInv_coeFn_ae_integral (𝓕 (hf.toLp f)) hg
  rw [fourierInv_fourier_eq] at he
  exact Measure.eq_of_ae_eq (hf.coeFn_toLp.symm.trans he) hcont
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hg)

end JanetCartan.ResponseTransfer.SourceNegative
