module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.LowSupport
/-!
# The low-envelope Fourier datum

L¹ control from low physical-frequency support, for both ordinary L¹ ∩ L²
inputs and the L² Fourier extension. These prerequisites are consumed by the
source-kernel reconstruction in `app:ch_response:thm:response-literal-transfer`.
-/

open MeasureTheory FourierTransform
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization
variable {n r : ℕ}
/-- The low-envelope Fourier L¹ estimate for an L¹ ∩ L² input, with the
exact manuscript normalization (`app:ch_response:thm:response-literal-transfer`).
The L² version below removes the physical L¹ assumption. -/
theorem paperFourierTransform_lowSupport_L1 {f : Euclidean n → EuclideanSpace ℂ (Fin r)}
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperFourierTransform f θ = 0) :
    Integrable (paperFourierTransform f) ∧
      (∫ θ, ‖paperFourierTransform f θ‖) ≤
        Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) * Λ ^ ((n : ℝ) / 2) *
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.sqrt (∫ x, ‖f x‖ ^ 2)) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hf₂.aestronglyMeasurable).mp hf₂
  have hm : MemLp (paperFourierTransform f) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm ?_).mpr
      (integrable_norm_sq_paperNormalizedFourierIntegral hf hsq)
    simp only [physicalFourierIntegral_eq_fourier]
    exact ((fourierIntegral_memLp_two hf hf₂).aestronglyMeasurable.comp_quasiMeasurePreserving
      (volume.quasiMeasurePreserving_smul
        (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0)))).const_smul _
  obtain ⟨hi, hb⟩ := integrable_and_integral_norm_le_of_lowSupport hm hΛ hs
  refine ⟨hi, ?_⟩
  convert hb using 1
  simp only [paperFourierTransform]
  rw [sqrt_integral_norm_sq_paperNormalizedFourierIntegral hf hsq]
  simp

/-- The L² extension of `Localization.paperFourierTransform`, in physical
frequency coordinates and with Lebesgue measure. This is the Fourier datum
used for the low-envelope reconstruction in
`app:ch_response:thm:response-literal-transfer`. -/
def paperL2FourierTransform (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (θ : Euclidean n) : EuclideanSpace ℂ (Fin r) :=
  ((2 * Real.pi) ^ n : ℝ)⁻¹ •
    (𝓕 f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
      ((2 * Real.pi)⁻¹ • θ)

private theorem integral_norm_sq_L2 (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- The physical, paper-normalized L² Fourier transform belongs to L²
(`app:ch_response:thm:response-literal-transfer`). -/
theorem paperL2FourierTransform_memLp (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) :
    MemLp (paperL2FourierTransform f) 2 volume := by
  have hm := Lp.memLp (𝓕 f)
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr
  · simp only [paperL2FourierTransform, norm_smul, mul_pow]
    exact (((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).comp_smul
      (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))).const_mul _
  · exact (((Lp.stronglyMeasurable (𝓕 f)).comp_measurable
      (measurable_const_smul ((2 * Real.pi : ℝ)⁻¹))).const_smul (((2 * Real.pi) ^ n : ℝ)⁻¹)).aestronglyMeasurable

/-- Exact Plancherel normalization for the low-envelope L² datum:
`(2π)^(-n/2)`, as used in `app:ch_response:thm:response-literal-transfer`. -/
theorem sqrt_integral_norm_sq_paperL2FourierTransform
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) :
    Real.sqrt (∫ θ, ‖paperL2FourierTransform f θ‖ ^ 2) =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖ := by
  have he : (∫ θ, ‖paperL2FourierTransform f θ‖ ^ 2) =
      ((2 * Real.pi) ^ n : ℝ)⁻¹ * ‖f‖ ^ 2 := by
    simp only [paperL2FourierTransform, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
      (fun θ ↦ ‖(𝓕 f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) θ‖ ^ 2)
      (by positivity : 0 ≤ 2 * Real.pi)]
    simp only [smul_eq_mul, finrank_euclideanSpace_fin, integral_norm_sq_L2, Lp.norm_fourier_eq]
    field_simp
    simp only [mul_pow]
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The low-envelope Fourier L¹ estimate for an arbitrary L² datum,
without physical L¹ or continuity assumptions
(`app:ch_response:thm:response-literal-transfer`). -/
theorem paperL2FourierTransform_lowSupport_L1
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    Integrable (paperL2FourierTransform f) ∧
      (∫ θ, ‖paperL2FourierTransform f θ‖) ≤
        Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) * Λ ^ ((n : ℝ) / 2) *
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ‖f‖) := by
  obtain ⟨hi, hb⟩ := integrable_and_integral_norm_le_of_lowSupport
    (paperL2FourierTransform_memLp f) hΛ hs
  exact ⟨hi, by simpa only [sqrt_integral_norm_sq_paperL2FourierTransform] using hb⟩
/-- The L² extension agrees almost everywhere with the literal ordinary
integral on L¹ ∩ L² (`app:ch_response:thm:response-literal-transfer`). -/
theorem paperL2FourierTransform_eq_paperFourierTransform_ae
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin r))) :
    paperL2FourierTransform f =ᵐ[volume]
      paperFourierTransform (f : Euclidean n → EuclideanSpace ℂ (Fin r)) := by
  have he := (volume.quasiMeasurePreserving_smul
    (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))).ae
      (fourierTransform_coeFn_ae_integral_hilbert f hf)
  filter_upwards [he] with θ hθ
  simp only [paperL2FourierTransform, paperFourierTransform,
    physicalFourierIntegral_eq_fourier, finrank_euclideanSpace_fin, hθ]

end JanetCartan.ResponseTransfer.LowEnvelope
