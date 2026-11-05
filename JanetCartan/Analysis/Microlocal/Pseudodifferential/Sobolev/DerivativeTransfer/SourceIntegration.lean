module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization

/-!
# Source integration by parts

The source-position identity for `app:ch_regular_base:eq:graph-derivative-transfer`,
proved from the Fourier integration-by-parts theorem on compact smooth data.
No differentiation of an oscillatory integral is postulated.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
/-- `app:ch_regular_base:eq:graph-derivative-transfer`: a directional derivative
of a compact smooth function transforms to multiplication by `2π i ⟪v, ξ⟫`.
Compact support discharges both integrability hypotheses of integration by parts. -/
theorem fourier_directionalDerivative_of_compactSupport (f : V → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (v ξ : V) :
    𝓕 (fun y ↦ fderiv ℝ f y v) ξ =
      (2 * Real.pi * Complex.I * (⟪v, ξ⟫ : ℝ)) * 𝓕 f ξ := by
  have hi : Integrable (fderiv ℝ f) := (hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hs.fderiv ℝ)
  rw [← Real.fourier_continuousLinearMap_apply hi, Real.fourier_fderiv
    (hf.continuous.integrable_of_hasCompactSupport hs) (hf.differentiable (by simp)) hi]
  simp only [VectorFourier.fourierSMulRight_apply]
  change -(2 * (Real.pi : ℂ) * Complex.I) • (-⟪ξ, v⟫) • 𝓕 f ξ = _
  rw [real_inner_comm ξ v]
  simp only [neg_smul, Complex.real_smul, smul_eq_mul]
  ring

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: source integration by
parts retains the derivative of the full source-dependent amplitude. The two
terms on the left exactly replace a phase derivative. -/
theorem sourceAmplitudeTransform_sourceDerivative_add_inputDerivative (c : V → V → V → ℂ) (u : V → ℂ) (x ξ v : V)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hc : ContDiff ℝ ∞ (fun y ↦ c x y ξ)) :
    sourceAmplitudeTransform (fun x y ξ ↦ fderiv ℝ (fun z ↦ c x z ξ) y v) u x ξ +
      sourceAmplitudeTransform c (fun y ↦ fderiv ℝ u y v) x ξ =
      (2 * Real.pi * Complex.I * (⟪v, ξ⟫ : ℝ)) * sourceAmplitudeTransform c u x ξ := by
  let f : V → ℂ := fun y ↦ u y * c x y ξ
  have hf : ContDiff ℝ ∞ f := hu.mul hc
  have hs : HasCompactSupport f := hus.mul_right
  have hfourier := fourier_directionalDerivative_of_compactSupport f hf hs v ξ
  have hdf : (fun y ↦ fderiv ℝ f y v) = fun y ↦
      u y * fderiv ℝ (fun z ↦ c x z ξ) y v + fderiv ℝ u y v * c x y ξ := by
    funext y
    dsimp only [f]
    rw [fderiv_fun_mul (hu.differentiable (by simp) y) (hc.differentiable (by simp) y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hdf] at hfourier
  have h₁ : Integrable (fun y ↦ u y * fderiv ℝ (fun z ↦ c x z ξ) y v) :=
    (hu.continuous.mul ((hc.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport hus.mul_right
  have h₂ : Integrable (fun y ↦ fderiv ℝ u y v * c x y ξ) :=
    (((hu.continuous_fderiv (by simp)).clm_apply continuous_const).mul hc.continuous).integrable_of_hasCompactSupport (hus.fderiv_apply ℝ v).mul_right
  simp only [Real.fourier_eq, smul_add] at hfourier
  rw [integral_add ((Real.fourierIntegral_convergent_iff ξ).mpr h₁)
    ((Real.fourierIntegral_convergent_iff ξ).mpr h₂)] at hfourier
  simpa only [sourceAmplitudeTransform, smul_eq_mul, Real.fourier_eq, f] using hfourier
end JanetCartan.Pseudodifferential
