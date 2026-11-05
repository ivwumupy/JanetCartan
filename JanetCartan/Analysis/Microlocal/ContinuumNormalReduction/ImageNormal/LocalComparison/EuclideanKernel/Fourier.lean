module
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.HeatMass
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.BesselSymbol
/-!
# Fourier transform of the literal image Bessel kernel

For `app:ch_background:prop:bg-frame`, Step 1, the heat representation gives
exactly `imageBesselSymbol` in unit-frequency coordinates. Joint absolute
integrability justifies Fubini, the finite-dimensional Gaussian Fourier formula
supplies the factor `2π`, and the half-order Gamma integral finishes the calculation.
The consumer is the Schwartz convolution realization and the local periodic comparison.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.Pseudodifferential
open scoped FourierTransform
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- The positive-time heat density has the physical heat symbol, including
`2π` (`app:ch_background:defn:bg-row`). -/
theorem fourier_imageBesselHeatKernel {t : ℝ} (ht : 0 < t) (ξ : E) :
    𝓕 (fun x : E ↦ (imageBesselHeatKernel t x : ℂ)) ξ =
      (Real.exp (-t * ‖(2 * Real.pi) • ξ‖ ^ 2) : ℂ) := by
  have he : (fun x : E ↦ (imageBesselHeatKernel t x : ℂ)) =
      (fun x : E ↦ ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) *
        Complex.exp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖x‖ ^ 2)) := by
    ext x
    simp only [imageBesselHeatKernel, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [he, Real.fourier_eq]
  simp_rw [← mul_smul_comm]
  rw [integral_const_mul]
  change _ * 𝓕 (fun x : E ↦ Complex.exp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖x‖ ^ 2)) ξ = _
  rw [fourier_gaussian_innerProductSpace (by simp; positivity), finrank_euclideanSpace_fin]
  have hp : (Real.pi : ℂ) / (((4 * t)⁻¹ : ℝ) : ℂ) = (4 * Real.pi * t : ℝ) := by
    push_cast
    rw [div_inv_eq_mul]
    ring
  have hd : (d : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, hd,
    ← Complex.ofReal_cpow (by positivity), ← mul_assoc, ← Complex.ofReal_mul]
  have hc : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      (4 * Real.pi * t) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity)]
    norm_num [show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring]
  rw [hc, Complex.ofReal_one, one_mul, Complex.ofReal_exp]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  push_cast
  rw [div_inv_eq_mul]
  ring

/-- Absolute integrability justifies taking the Fourier transform inside
the actual heat integral (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem fourier_imageBesselKernel_heatIntegral (ξ : E) :
    𝓕 (fun x : E ↦ (imageBesselKernel x : ℂ)) ξ =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * ∫ t : ℝ in Ioi 0,
        ((t ^ (-(1 : ℝ) / 2) * Real.exp (-t) : ℝ) : ℂ) *
          (Real.exp (-t * ‖(2 * Real.pi) • ξ‖ ^ 2) : ℂ) := by
  let F : ℝ × E → ℂ := fun p ↦ Real.fourierChar (-inner ℝ p.2 ξ) •
    ((p.1 ^ (-(1 : ℝ) / 2) * Real.exp (-p.1) * imageBesselHeatKernel p.1 p.2 : ℝ) : ℂ)
  have hi : Integrable F ((volume.restrict (Ioi 0)).prod volume) := by
    apply integrable_imageBesselHeatIntegrand.norm.mono'
    · exact (Real.continuous_fourierChar.comp
        ((continuous_snd.inner continuous_const).neg)).aestronglyMeasurable.fun_smul
          integrable_imageBesselHeatIntegrand.ofReal.aestronglyMeasurable
    · filter_upwards with p
      dsimp only [F]
      rw [Circle.norm_smul, Complex.norm_real]
  rw [Real.fourier_eq]
  simp only [imageBesselKernel, Complex.ofReal_mul, ← integral_complex_ofReal,
    Circle.smul_def, smul_eq_mul]
  simp_rw [mul_left_comm (Real.fourierChar (-inner ℝ _ ξ) : ℂ)
    (((Real.sqrt Real.pi)⁻¹ : ℝ) : ℂ)]
  rw [integral_const_mul, Complex.ofReal_inv]
  congr 1
  simp_rw [← integral_const_mul]
  simp_rw [← Complex.ofReal_mul]
  change (∫ x : E, ∫ t : ℝ in Ioi 0, F (t, x)) = _
  rw [← integral_integral_swap hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [F]
  simp only [Complex.ofReal_mul]
  simp_rw [← mul_smul_comm]
  rw [integral_const_mul]
  change _ * 𝓕 (fun x : E ↦ (imageBesselHeatKernel t x : ℂ)) ξ = _
  rw [fourier_imageBesselHeatKernel ht]

/-- The literal heat kernel has exactly the image inverse symbol
(`app:ch_background:defn:bg-row`); no Fourier identification is assumed. -/
theorem fourier_imageBesselKernel (ξ : E) :
    𝓕 (fun x : E ↦ (imageBesselKernel x : ℂ)) ξ = (imageBesselSymbol ξ : ℂ) := by
  rw [fourier_imageBesselKernel_heatIntegral]
  have he : (∫ t : ℝ in Ioi 0,
      ((t ^ (-(1 : ℝ) / 2) * Real.exp (-t) : ℝ) : ℂ) *
        (Real.exp (-t * ‖(2 * Real.pi) • ξ‖ ^ 2) : ℂ)) =
      ((∫ t : ℝ in Ioi 0, t ^ ((1 : ℝ) / 2 - 1) *
        Real.exp (-((1 + ‖(2 * Real.pi) • ξ‖ ^ 2) * t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity),
    Real.Gamma_one_half_eq]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [imageBesselSymbol, euclideanSobolevWeight]
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  rw [mul_comm _ (Real.sqrt Real.pi), ← mul_assoc, inv_mul_cancel₀ hs, one_mul,
    one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 1
  norm_num

end JanetCartan.ContinuumNormalReduction.ImageNormal
