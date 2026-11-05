module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The physical Fourier transform of the source cutoff

The hat in `app:ch_regular_base:eq:fixed-source-multiplication` includes
`(2π)⁻ⁿ`. Its inverse integral consequently has no prefactor. All integrals
here use Euclidean Lebesgue measure, with the same covectors as `graphOperator`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace JanetCartan.FourierIntegral

/-- Normalized physical Fourier transform of a Schwartz source cutoff, for
`app:ch_regular_base:eq:fixed-source-multiplication`. Compactly supported smooth
cutoffs are supplied using `HasCompactSupport.toSchwartzMap`. -/
def sourceFourierTransform {n : ℕ} (m : SchwartzMap (Euclidean n) ℂ) :
    SchwartzMap (Euclidean n) ℂ :=
  ((2 * Real.pi) ^ n : ℝ)⁻¹ •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean n)
        (Units.mk0 (2 * Real.pi)⁻¹ (by positivity))) (𝓕 m)

/-- The precise change of frequency variables in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceFourierTransform_apply {n : ℕ} (m : SchwartzMap (Euclidean n) ℂ)
    (v : Euclidean n) :
    sourceFourierTransform m v = ((2 * Real.pi) ^ n : ℝ)⁻¹ •
      𝓕 (m : Euclidean n → ℂ) ((2 * Real.pi)⁻¹ • v) := rfl

/-- All absolute polynomial moments required by
`app:ch_regular_base:eq:fixed-source-multiplication` are finite. -/
theorem sourceFourierTransform_integrable_moment {n : ℕ}
    (m : SchwartzMap (Euclidean n) ℂ) (k : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ k * ‖sourceFourierTransform m v‖) :=
  (sourceFourierTransform m).integrable_pow_mul volume k

/-- The transform used in the source symbol is the literal normalized physical
Fourier integral, with the sign and prefactor of
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceFourierTransform_eq_integral {n : ℕ}
    (m : SchwartzMap (Euclidean n) ℂ) (v : Euclidean n) :
    sourceFourierTransform m v = ((2 * Real.pi) ^ n : ℝ)⁻¹ •
      ∫ y, Complex.exp (Complex.I * (-(inner ℝ y v) : ℝ)) * m y := by
  rw [sourceFourierTransform_apply, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [real_inner_smul_right, smul_eq_mul]
  congr 2
  have h : -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ y v) = -inner ℝ y v := by
    field_simp
  rw [h, mul_comm]

/-- Actual Schwartz Fourier inversion in physical covectors. This supplies the
principal term of `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceFourierTransform_inversion {n : ℕ}
    (m : SchwartzMap (Euclidean n) ℂ) (y : Euclidean n) :
    (∫ v, Complex.exp (Complex.I * (inner ℝ y v : ℂ)) *
      sourceFourierTransform m v) = m y := by
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun v : Euclidean n ↦ Complex.exp ((2 * Real.pi * inner ℝ v y : ℝ) * Complex.I) *
      𝓕 (m : Euclidean n → ℂ) v) (show 0 ≤ 2 * Real.pi by positivity)
  simp only [Euclidean, finrank_euclideanSpace_fin] at hscale
  have hphase (v : Euclidean n) :
      Complex.exp (Complex.I * (inner ℝ y v : ℂ)) =
        Complex.exp ((2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ • v) y : ℝ) * Complex.I) := by
    rw [real_inner_smul_left, real_inner_comm v y]
    congr 1
    push_cast
    field_simp
  simp_rw [sourceFourierTransform_apply, hphase, mul_smul_comm]
  rw [integral_smul, hscale, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  have hinv := congrArg (fun f : SchwartzMap (Euclidean n) ℂ ↦ f y)
    (fourierInv_fourier_eq (F := SchwartzMap (Euclidean n) ℂ) m)
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
    Real.fourierInv_eq', smul_eq_mul] using hinv

end JanetCartan.FourierIntegral
