module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Regularization
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MultiplierKernel.IntegralFourier

/-!
# Integral realization of compact-frequency multipliers

The compact-frequency kernel in `app:ch_osc:lem:osc-amplitude` uses the unit-period
Fourier convention, with phase `exp (2π i ⟪x-y, ξ⟫)` and no normalization factor.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ENNReal

namespace JanetCartan.AmplitudeBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The compact frequency product is integrable, even for arbitrary L² frequency
data (`app:ch_osc:lem:osc-amplitude`). -/
theorem integrable_multiplicationOperator_compactFrequencySymbol
    (ρ : ℝ) (a : Lp (α := E) ℂ ∞) (f : Lp (α := E) ℂ 2) :
    Integrable (multiplicationOperator (compactFrequencySymbol ρ a) f : E → ℂ) := by
  let g := multiplicationOperator (compactFrequencySymbol ρ a) f
  have hi := ((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0 : E) ρ)
  apply (hi.integrable_indicator measurableSet_closedBall).congr
  filter_upwards [multiplicationOperator_coeFn (compactFrequencySymbol ρ a) f,
    truncateSymbol_coeFn (Metric.closedBall 0 ρ) measurableSet_closedBall a] with ξ hg ha
  by_cases hξ : ξ ∈ Metric.closedBall (0 : E) ρ
  · simp only [Set.indicator_of_mem hξ]
    rfl
  · change (Metric.closedBall 0 ρ).indicator g ξ = g ξ
    rw [Set.indicator_of_notMem hξ]
    change 0 = multiplicationOperator (compactFrequencySymbol ρ a) f ξ
    rw [hg]
    change 0 = truncateSymbol (Metric.closedBall 0 ρ) measurableSet_closedBall a ξ * f ξ
    rw [ha, Set.indicator_of_notMem hξ, zero_mul]

/-- The scalar Fourier phases combine into the two-position kernel from
`app:ch_osc:lem:osc-amplitude`. -/
theorem fourier_phase_mul_integral (a : E → ℂ) (f : E → ℂ) (x ξ : E) :
    (Real.fourierChar ⟪ξ, x⟫ : ℂ) * (a ξ * 𝓕 f ξ) =
      ∫ y, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ * f y := by
  rw [Real.fourier_eq, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Circle.smul_def, smul_eq_mul]
  have hp : (Real.fourierChar ⟪ξ, x⟫ : ℂ) * (Real.fourierChar (-⟪y, ξ⟫) : ℂ) =
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) := by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
    congr 1
    rw [inner_sub_left, real_inner_comm ξ x]
    push_cast
    ring
  calc
    _ = ((Real.fourierChar ⟪ξ, x⟫ : ℂ) *
        (Real.fourierChar (-⟪y, ξ⟫) : ℂ)) * a ξ * f y := by ring
    _ = _ := by rw [hp]

/-- Absolute integrability of the compact-frequency kernel in both integration
variables (`app:ch_osc:lem:osc-amplitude`). In particular its product-measure
measurability and the hypotheses for Fubini follow from the stated assumptions. -/
theorem integrable_compactFrequency_kernel
    (ρ : ℝ) (a : Lp (α := E) ℂ ∞) {f : E → ℂ} (hf : Integrable f) (x : E) :
    Integrable (fun p : E × E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I) * a p.1 * f p.2)
      ((volume.restrict (Metric.closedBall 0 ρ)).prod volume) := by
  have ha := ((Lp.memLp a).locallyIntegrable (by simp)).integrableOn_isCompact
    (isCompact_closedBall (0 : E) ρ)
  have hp : Continuous (fun p : E × E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - p.2, p.1⟫) * Complex.I)) := by fun_prop
  apply (ha.norm.mul_prod hf.norm).mono'
  · exact (hp.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable a).restrict.comp_fst).mul hf.aestronglyMeasurable.comp_snd
  · filter_upwards with p
    simp only [norm_mul, ← Real.fourierChar_apply, Circle.norm_coe, one_mul, le_refl]

/-- For each frequency the physical integral in the kernel from
`app:ch_osc:lem:osc-amplitude` is absolutely convergent. -/
theorem integrable_compactFrequency_kernel_inner
    (a : E → ℂ) {f : E → ℂ} (hf : Integrable f) (x ξ : E) :
    Integrable (fun y ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ * f y) := by
  have hp : Continuous (fun y : E ↦
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ) := by fun_prop
  apply (hf.norm.const_mul ‖a ξ‖).mono' (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with y
  simp only [Pi.mul_apply, norm_mul, ← Real.fourierChar_apply, Circle.norm_coe, one_mul, le_refl]

/-- Absolute convergence of the outer frequency integral in
`app:ch_osc:lem:osc-amplitude`. -/
theorem integrableOn_compactFrequency_kernel_integral
    (ρ : ℝ) (a : Lp (α := E) ℂ ∞) {f : E → ℂ} (hf : Integrable f) (x : E) :
    IntegrableOn (fun ξ ↦ ∫ y,
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ * f y)
      (Metric.closedBall 0 ρ) :=
  (integrable_compactFrequency_kernel ρ a hf x).integral_prod_left

/-- The compact-frequency L² multiplier is the literal iterated integral in
`app:ch_osc:lem:osc-amplitude` for every integrable L² input, almost everywhere.
The frequency is the unit-period frequency, so there is no normalization factor. -/
theorem fourierMultiplier_compactFrequencySymbol_ae_kernel
    (ρ : ℝ) (a : Lp (α := E) ℂ ∞) (f : Lp (α := E) ℂ 2)
    (hf : Integrable (f : E → ℂ)) :
    fourierMultiplier (compactFrequencySymbol ρ a) f =ᵐ[volume]
      fun x ↦ ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ * f y := by
  let g := multiplicationOperator (compactFrequencySymbol ρ a) (𝓕 f)
  have hg := fourierTransformInv_coeFn_ae_integral g
    (integrable_multiplicationOperator_compactFrequencySymbol ρ a (𝓕 f))
  have hrep : (g : E → ℂ) =ᵐ[volume]
      (Metric.closedBall 0 ρ).indicator (fun ξ ↦ a ξ * 𝓕 (f : E → ℂ) ξ) := by
    filter_upwards [multiplicationOperator_coeFn (compactFrequencySymbol ρ a) (𝓕 f),
      truncateSymbol_coeFn (Metric.closedBall 0 ρ) measurableSet_closedBall a,
      fourierTransform_coeFn_ae_integral f hf] with ξ hm ha hF
    change multiplicationOperator (compactFrequencySymbol ρ a) (𝓕 f) ξ = _
    rw [hm, hF]
    change truncateSymbol (Metric.closedBall 0 ρ) measurableSet_closedBall a ξ * _ = _
    rw [ha]
    by_cases hξ : ξ ∈ Metric.closedBall (0 : E) ρ <;> simp [hξ]
  change ((𝓕⁻ g : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume] _
  filter_upwards [hg] with x hx
  rw [hx, Real.fourierInv_congr_ae hrep x, Real.fourierInv_eq]
  calc
    _ = ∫ ξ, (Metric.closedBall 0 ρ).indicator
        (fun ξ ↦ (Real.fourierChar ⟪ξ, x⟫ : ℂ) * (a ξ * 𝓕 (f : E → ℂ) ξ)) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      by_cases hξ : ξ ∈ Metric.closedBall (0 : E) ρ <;>
        simp [hξ, Circle.smul_def]
    _ = _ := by
      rw [integral_indicator measurableSet_closedBall]
      apply setIntegral_congr_fun measurableSet_closedBall
      intro ξ _
      exact fourier_phase_mul_integral a f x ξ

/-- The realized kernel defines a measurable square-integrable function of the
output position (`app:ch_osc:lem:osc-amplitude`). -/
theorem memLp_compactFrequency_kernel_integral
    (ρ : ℝ) (a : Lp (α := E) ℂ ∞) (f : Lp (α := E) ℂ 2)
    (hf : Integrable (f : E → ℂ)) :
    MemLp (fun x ↦ ∫ ξ in Metric.closedBall 0 ρ, ∫ y,
      Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) * a ξ * f y) 2 :=
  (memLp_congr_ae (fourierMultiplier_compactFrequencySymbol_ae_kernel ρ a f hf)).mp
    (Lp.memLp _)

end JanetCartan.AmplitudeBound
