module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.CompactFrequency.Kernel

/-!
# Compact-frequency Fubini and source transfer

The source Fourier identity in `app:ch_regular_base:eq:graph-derivative-transfer`
passes through the literal compact-frequency kernel using compact supports.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff RealInnerProductSpace FourierTransform
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_frequency_source_product
    {f : E × E → ℂ} (hf : Continuous f) (ρ : ℝ)
    {u : E → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) :
    Integrable (fun p : E × E ↦ f p * u p.2)
      ((volume.restrict (Metric.closedBall 0 ρ)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) ρ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : E) ρ).measure_lt_top.ne
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E) ρ).prod hus).exists_bound_of_continuousOn
    hf.continuousOn
  apply ((integrable_const C).mul_prod
    (hu.integrable_of_hasCompactSupport hus).norm).mono'
  · exact (hf.mul (hu.comp continuous_snd)).aestronglyMeasurable
  · rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [ae_restrict_mem measurableSet_closedBall] with ξ hξ
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport u
      · simpa only [norm_mul] using
          mul_le_mul_of_nonneg_right (hC (ξ, y) ⟨hξ, hy⟩) (norm_nonneg (u y))
      · simp [image_eq_zero_of_notMem_tsupport hy]
    · exact measurableSet_le (by fun_prop) (by fun_prop)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: absolute joint
integrability in the frequency ball and source position follows from continuity
and compact support of the datum. -/
theorem integrable_compactFrequencyAmplitudeKernel_source_integrand
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : Continuous (Function.uncurry b)) (ρ : ℝ)
    {u : E → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) (x : E) :
    Integrable (fun p : E × E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) *
        b p.1 (pairedPosition x p.2) * u p.2)
      ((volume.restrict (Metric.closedBall 0 ρ)).prod volume) := by
  apply integrable_frequency_source_product _ ρ hu hus
  exact (by fun_prop : Continuous (fun p : E × E ↦
    Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I))).mul
      (hb.comp (continuous_fst.prodMk
        (continuous_pairedPosition.comp (continuous_const.prodMk continuous_snd))))

private theorem phased_source_integral
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (u : E → ℂ) (x ξ : E) :
    (∫ y, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
      b ξ (pairedPosition x y) * u y) =
      Real.fourierChar ⟪ξ, x⟫ •
        sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) u x ξ := by
  unfold sourceAmplitudeTransform
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, Real.fourierChar_apply]
  rw [show ⟪ξ, x⟫ + -⟪y, ξ⟫ = ⟪x - y, ξ⟫ by
    simp only [inner_sub_left]
    rw [real_inner_comm ξ x]
    ring]
  ring

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: Fubini identifies the
literal physical kernel acting on compact continuous data with the truncated
source Fourier transform. No global amplitude bound is needed. -/
theorem compactFrequencyAmplitudeKernel_integral_eq_sourceIntegral
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : Continuous (Function.uncurry b)) (ρ : ℝ)
    {u : E → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) (x : E) :
    (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y) =
      ∫ ξ in Metric.closedBall 0 ρ, Real.fourierChar ⟪ξ, x⟫ •
        sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) u x ξ := by
  simp only [compactFrequencyAmplitudeKernel, ← integral_mul_const]
  rw [← integral_integral_swap
    (integrable_compactFrequencyAmplitudeKernel_source_integrand hb ρ hu hus x)]
  simp_rw [phased_source_integral]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the truncated phased
source transform is integrable, as a consequence of joint compact integrability. -/
theorem integrableOn_compactFrequency_sourceIntegral
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : Continuous (Function.uncurry b)) (ρ : ℝ)
    {u : E → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) (x : E) :
    IntegrableOn (fun ξ ↦ Real.fourierChar ⟪ξ, x⟫ •
      sourceAmplitudeTransform (fun x y ξ ↦ b ξ (pairedPosition x y)) u x ξ)
      (Metric.closedBall 0 ρ) := by
  have h := (integrable_compactFrequencyAmplitudeKernel_source_integrand hb ρ hu hus x).integral_prod_left
  simpa only [IntegrableOn, phased_source_integral] using h

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: source integration by
parts transfers the output derivative through the compact-frequency kernel. -/
theorem compactFrequencyAmplitudeKernel_outputDerivative_eq_transfer
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (ρ : ℝ) (i : Fin d)
    {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (x : E) :
    (∫ y, compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y * u y) =
      (∫ y, compactFrequencyAmplitudeKernel (transferAmplitude b i) ρ x y * u y) +
      (∫ y, compactFrequencyAmplitudeKernel b ρ x y *
        fderiv ℝ u y (EuclideanSpace.single i 1)) := by
  have hdu := (hu.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := EuclideanSpace.single i 1))
  have hdus := hus.fderiv_apply ℝ (EuclideanSpace.single i 1)
  rw [compactFrequencyAmplitudeKernel_integral_eq_sourceIntegral
      (contDiff_uncurry_outputDerivativeAmplitude hb i).continuous ρ hu.continuous hus,
    compactFrequencyAmplitudeKernel_integral_eq_sourceIntegral
      (contDiff_uncurry_transferAmplitude hb i).continuous ρ hu.continuous hus,
    compactFrequencyAmplitudeKernel_integral_eq_sourceIntegral hb.continuous ρ hdu hdus]
  simp_rw [sourceAmplitudeTransform_outputDerivativeAmplitude b
    (fun ξ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i u hu hus, smul_add]
  exact integral_add
    (integrableOn_compactFrequency_sourceIntegral
      (contDiff_uncurry_transferAmplitude hb i).continuous ρ hu.continuous hus x)
    (integrableOn_compactFrequency_sourceIntegral hb.continuous ρ hdu hdus x)

end JanetCartan.Pseudodifferential
