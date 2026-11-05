module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteFourier
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.TemporalIntegral

/-!
# Absolute convergence and continuity of the finite-budget temporal slice

A zeroth-order bound on the original multiplier and Schwartz decay of the
original test suffice for the temporal integral, spatial integrability,
continuity and Fubini. The finite derivative reserve is used separately for
integrability of the physical inverse's spatial restrictions. Consumer:
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology ContDiff
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The uncut temporal integrand is integrable on every fiber under only the
zeroth-order multiplier bound. This bound is produced by
`norm_multiplier_le_finite_normalized_budgets`. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_uncutTemporalFourierIntegrand_of_bound
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) (s : ℝ) (η : Euclidean d) :
    Integrable (cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η) := by
  let f := temporalSchwartzFiber (sourceInputFourierTransform v) η
  apply (f.integrable.norm.const_mul C).mono'
  · exact (show Continuous (cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η) by
      unfold cutTemporalFourierIntegrand
      exact (by fun_prop : Continuous (fun τ : ℝ ↦ Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ))))
        |>.smul ((continuous_const.mul (hβ.comp (continuous_timeSpacePoint.comp
          (continuous_id.prodMk continuous_const)))).smul f.continuous)).aestronglyMeasurable
  · filter_upwards [] with τ
    simp only [cutTemporalFourierIntegrand, one_mul, norm_smul, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)

private theorem integrable_timeModulation_of_bound
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) (s : ℝ) :
    Integrable (fun ξ : E ↦ Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)) •
      (β ξ • sourceInputFourierTransform v ξ)) := by
  apply (integrable_multiplierFrequencyData β hβ v C hbound).norm.mono'
  · exact ((by fun_prop : Continuous (fun ξ : E ↦
      Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)))).smul
        (hβ.smul (sourceInputFourierTransform v).continuous)).aestronglyMeasurable
  · filter_upwards [] with ξ
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
      one_mul, le_refl]

/-- The literal temporal slice is integrable in spatial frequency using the
original order-zero bound and Fubini. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_uncutTemporalFourierSlice_of_bound
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) (s : ℝ) :
    Integrable (cutTemporalFourierSlice β (fun _ ↦ 1) v s) := by
  have hp := measurePreserving_timeSpaceMeasurableEquiv (d := d)
  have hi := hp.symm.integrable_comp_of_integrable
    (integrable_timeModulation_of_bound β hβ v C hbound s)
  change Integrable (fun p : ℝ × Euclidean d ↦
    Complex.exp (Complex.I * ((s * (timeSpacePoint p.1 p.2) 0 : ℝ) : ℂ)) •
      (β (timeSpacePoint p.1 p.2) • sourceInputFourierTransform v (timeSpacePoint p.1 p.2)))
      (volume.prod volume) at hi
  simp only [timeSpacePoint_time] at hi
  unfold cutTemporalFourierSlice
  convert! hi.integral_prod_right.smul (2 * Real.pi : ℂ)⁻¹ using 1
  simp only [cutTemporalFourierIntegrand, one_mul]
  rfl

/-- The temporal inverse is continuous in spatial frequency from a single
Schwartz majorant and the finite zeroth-order symbol bound. Consumer: pointwise
Fourier inversion in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_uncutTemporalFourierSlice_of_bound
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) (s : ℝ) :
    Continuous (cutTemporalFourierSlice β (fun _ ↦ 1) v s) := by
  have hC : 0 ≤ C := (norm_nonneg (β 0)).trans (hbound 0)
  let f := sourceInputFourierTransform v
  unfold cutTemporalFourierSlice
  refine (show Continuous (fun η : Euclidean d ↦
    ∫ τ : ℝ, cutTemporalFourierIntegrand β (fun _ ↦ 1) v s η τ) from ?_).const_smul (2 * Real.pi : ℂ)⁻¹
  apply continuous_of_dominated (bound := fun τ : ℝ ↦
    C * ((SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + τ ^ 2)⁻¹))
  · intro η
    exact (integrable_uncutTemporalFourierIntegrand_of_bound β hβ v C hbound s η).aestronglyMeasurable
  · intro η
    filter_upwards [] with τ
    simp only [cutTemporalFourierIntegrand, one_mul, norm_smul, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul (hbound _) (norm_temporalSchwartzFiber_le_integrable_majorant f τ η) (norm_nonneg _) hC
  · exact (integrable_inv_one_add_sq.const_mul _).const_mul C
  · filter_upwards [] with τ
    unfold cutTemporalFourierIntegrand
    exact (continuous_const (y := Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)))).smul
      (((continuous_const (y := (1 : ℂ))).mul (hβ.comp
      (continuous_timeSpacePoint.comp (continuous_const.prodMk continuous_id)))).smul
        (f.continuous.comp (continuous_timeSpacePoint.comp (continuous_const.prodMk continuous_id))))

/-- Fubini splits the original multiplier's physical inverse into the spatial
inverse of its temporal integral. Every integral is justified by the original
test and only a zeroth-order bound on `β`; no Schwartz output is postulated.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalMultiplierIntegral_eq_spatialInverse
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) (s : ℝ) (y : Euclidean d) :
    physicalMultiplierIntegral β v (timeSpacePoint s y) =
      ((2 * Real.pi) ^ d : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (inner ℝ y η : ℂ)) •
          cutTemporalFourierSlice β (fun _ ↦ 1) v s η := by
  rw [physicalMultiplierIntegral_eq_integral]
  have hi : Integrable (fun ξ : E ↦
      Complex.exp (Complex.I * (inner ℝ (timeSpacePoint s y) ξ : ℂ)) •
        (β ξ • sourceInputFourierTransform v ξ)) := by
    apply (integrable_multiplierFrequencyData β hβ v C hbound).norm.mono'
    · exact ((by fun_prop : Continuous (fun ξ : E ↦
        Complex.exp (Complex.I * (inner ℝ (timeSpacePoint s y) ξ : ℂ)))).smul
          (hβ.smul (sourceInputFourierTransform v).continuous)).aestronglyMeasurable
    · filter_upwards [] with ξ
      simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
        one_mul, le_refl]
  rw [integral_eq_space_time _ hi]
  simp only [inner_eq_time_add_spatial, timeSpacePoint_time,
    spatialPart_timeSpacePoint, Complex.ofReal_add, mul_add, Complex.exp_add,
    mul_smul, cutTemporalFourierSlice, cutTemporalFourierIntegrand, one_mul]
  simp_rw [smul_comm (Complex.exp (Complex.I * ((s * _ : ℝ) : ℂ))), integral_smul,
    smul_comm _ ((2 * Real.pi : ℂ)⁻¹), integral_smul, smul_smul]
  congr 1
  rw [pow_succ, mul_inv_rev]
  exact mul_comm _ _

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
