module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration.Trades

/-!
# Weak meaning of the Fourier-side derivative operators

For `app:ch_background:prop:bg-adjoint`, carrier differentiation is weak
differentiation against compact smooth carrier tests with the actual product
Lebesgue measure. Initial differentiation is weak physical differentiation of
each inverse-Fourier mode, with the radian convention `exp(i⟪y,η⟫)`.
These identities require no frequency cutoff and make no assertion about
interchanging an unbounded inverse-Fourier integral; that identification belongs
to the parent construction.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

private theorem weak_smooth_mul_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f ψ : E → ℂ} (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (h : E) :
    (∫ x, fderiv ℝ f x h * ψ x ∂μ) = -(∫ x, f x * fderiv ℝ ψ x h ∂μ) := by
  have hf' : Continuous (fun x ↦ fderiv ℝ f x h) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ' : Continuous (fun x ↦ fderiv ℝ ψ x h) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := h)
    ((hf'.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hf.continuous.mul hψ').integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ h).mul_left)
    ((hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun x _ ↦ hf.differentiable (by simp) x) (fun x _ ↦ hψ.differentiable (by simp) x)
  exact neg_eq_iff_eq_neg.mp hd.symm

/-- The shared carrier derivative is a weak derivative with the original
`dz = ds dv` measure (`app:ch_background:prop:bg-adjoint`). -/
theorem weak_carrier_applyInitialCarrierDerivative
    {f : CarrierVariable n → ℂ} (η : Euclidean (n - 1))
    (hf : ContDiff ℝ ∞ (fun z ↦ f (z, η)))
    {ψ : CarrierParameter → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (h : CarrierParameter) :
    (∫ z, applyInitialCarrierDerivative (.carrier h) f (z, η) * ψ z
      ∂(volume.prod volume)) =
      -(∫ z, f (z, η) * fderiv ℝ ψ z h ∂(volume.prod volume)) :=
  weak_smooth_mul_test hf hψ hs h

private theorem fderiv_initial_mode (η y h : Euclidean (n - 1)) (c : ℂ) :
    fderiv ℝ (fun w ↦ Complex.exp (Complex.I * (inner ℝ w η : ℂ)) * c) y h =
      Complex.exp (Complex.I * (inner ℝ y η : ℂ)) * ((Complex.I * (inner ℝ h η : ℂ)) * c) := by
  have hd := (((Complex.ofRealCLM.hasFDerivAt.comp y
    ((innerSL ℝ η).hasFDerivAt)).const_mul Complex.I).cexp.mul_const c).fderiv
  have he : (fun w : Euclidean (n - 1) ↦
      Complex.exp (Complex.I * (inner ℝ w η : ℂ)) * c) =
      fun w ↦ Complex.exp (Complex.I * (inner ℝ η w : ℂ)) * c := by
    ext w
    rw [real_inner_comm w η]
  simp only [Function.comp_def, Complex.ofRealCLM_apply, innerSL_apply_apply] at hd
  rw [he, hd]
  simp [ContinuousLinearMap.comp_apply, real_inner_comm η y, real_inner_comm η h,
    mul_comm, mul_left_comm]

/-- The initial operator is weak physical differentiation of each
inverse-Fourier mode, never differentiation in frequency
(`app:ch_background:eq:bg-derivative-trade`). This applies in particular when
`f` is any ordered derivative of the chart adjoint. -/
theorem weak_initial_applyInitialCarrierDerivative
    (f : CarrierVariable n → ℂ) (z : CarrierParameter) (η h : Euclidean (n - 1))
    {ψ : Euclidean (n - 1) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) :
    (∫ y, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) *
      applyInitialCarrierDerivative (.initial h) f (z, η) * ψ y) =
      -(∫ y, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) *
        f (z, η) * fderiv ℝ ψ y h) := by
  have hf : ContDiff ℝ ∞ (fun y : Euclidean (n - 1) ↦
      Complex.exp (Complex.I * (inner ℝ y η : ℂ)) * f (z, η)) :=
    by
      have hi : ContDiff ℝ ∞ (fun y : Euclidean (n - 1) ↦ (inner ℝ η y : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp ((innerSL ℝ η).contDiff)
      have hc := ((contDiff_const (c := Complex.I)).mul hi).cexp.mul
        (contDiff_const (c := f (z, η)))
      simpa only [real_inner_comm η] using hc
  simpa only [fderiv_initial_mode, applyInitialCarrierDerivative] using
    weak_smooth_mul_test hf hψ hs h

end JanetCartan.ContinuumAdjoint.DerivativeKernels
