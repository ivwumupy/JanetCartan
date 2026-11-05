module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.SchwartzSlices

/-!
# Uncut temporal Fourier slices

Absolute convergence and continuity of the temporal integral follow from the
Schwartz frequency datum. Fubini and Fourier inversion then identify it with
the spatial Fourier transform of the actual physical slice. This is the uncut
multiplier-slice step in `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- Temporal inversion of an uncut Schwartz frequency datum, with the
physical factor `(2π)⁻¹`. Consumer: the original multiplier-slice identity in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalTemporalIntegral (f : SchwartzMap E V) (s : ℝ) (η : Euclidean d) : V :=
  (2 * Real.pi : ℂ)⁻¹ • ∫ τ : ℝ,
    Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) • f (timeSpacePoint τ η)

/-- Every temporal integral is absolutely convergent, including exceptional
fibers that a bare Fubini assertion would leave unspecified. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_physicalTemporalIntegrand (f : SchwartzMap E V)
    (s : ℝ) (η : Euclidean d) :
    Integrable (fun τ : ℝ ↦
      Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) • f (timeSpacePoint τ η)) := by
  apply (temporalSchwartzFiber f η).integrable.norm.mono'
  · exact (by fun_prop : Continuous (fun τ : ℝ ↦
      Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) •
        temporalSchwartzFiber f η τ)).aestronglyMeasurable
  · filter_upwards [] with τ
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
      one_mul, temporalSchwartzFiber_apply, le_refl]

private theorem integrable_timeModulation (f : SchwartzMap E V) (s : ℝ) :
    Integrable (fun ξ : E ↦ Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)) • f ξ) := by
  apply f.integrable.norm.mono'
  · exact (by fun_prop : Continuous (fun ξ : E ↦
      Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)) • f ξ)).aestronglyMeasurable
  · filter_upwards [] with ξ
    simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
      one_mul, le_refl]

/-- The temporal inverse is integrable in the remaining spatial frequency.
This is proved by the measure-preserving coordinate split and Fubini, without
a cutoff. Consumer: spatial Fourier inversion in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_physicalTemporalIntegral (f : SchwartzMap E V) (s : ℝ) :
    Integrable (physicalTemporalIntegral f s) := by
  have hp := measurePreserving_timeSpaceMeasurableEquiv (d := d)
  have hi := hp.symm.integrable_comp_of_integrable (integrable_timeModulation f s)
  change Integrable (fun p : ℝ × Euclidean d ↦
    Complex.exp (Complex.I * ((s * (timeSpacePoint p.1 p.2) 0 : ℝ) : ℂ)) •
      f (timeSpacePoint p.1 p.2)) (volume.prod volume) at hi
  simp only [timeSpacePoint_time] at hi
  exact hi.integral_prod_right.smul (2 * Real.pi : ℂ)⁻¹

/-- A single quadratic majorant controls every temporal fiber of the original
Schwartz datum. Consumer: finite-budget temporal dominated convergence in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem norm_temporalSchwartzFiber_le_integrable_majorant (f : SchwartzMap E V) (τ : ℝ) (η : Euclidean d) :
    ‖f (timeSpacePoint τ η)‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + τ ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h0 := f.norm_le_seminorm ℝ (timeSpacePoint τ η)
  have h2 := f.norm_pow_mul_le_seminorm ℝ 2 (timeSpacePoint τ η)
  have ht : τ ^ 2 ≤ ‖timeSpacePoint τ η‖ ^ 2 := by
    have ht := PiLp.norm_apply_le (timeSpacePoint τ η) 0
    simp only [timeSpacePoint_time, Real.norm_eq_abs] at ht
    nlinarith [sq_abs τ, abs_nonneg τ, norm_nonneg (timeSpacePoint τ η)]
  nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg (f (timeSpacePoint τ η)))]

/-- A single integrable temporal majorant proves continuity of the uncut
temporal inverse in spatial frequency. Consumer: pointwise Fourier inversion
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_physicalTemporalIntegral (f : SchwartzMap E V) (s : ℝ) :
    Continuous (physicalTemporalIntegral f s) := by
  unfold physicalTemporalIntegral
  refine (show Continuous (fun η : Euclidean d ↦ ∫ τ : ℝ,
    Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) • f (timeSpacePoint τ η)) from ?_).const_smul
      (2 * Real.pi : ℂ)⁻¹
  apply continuous_of_dominated (bound := fun τ : ℝ ↦
    (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f) * (1 + τ ^ 2)⁻¹)
  · intro η
    exact (integrable_physicalTemporalIntegrand f s η).aestronglyMeasurable
  · intro η
    filter_upwards [] with τ
    simpa only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
      one_mul] using norm_temporalSchwartzFiber_le_integrable_majorant f τ η
  · exact integrable_inv_one_add_sq.const_mul _
  · filter_upwards [] with τ
    exact (continuous_const (y := Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)))).smul
      (f.continuous.comp (continuous_timeSpacePoint.comp
        (continuous_const.prodMk continuous_id)))

/-- Full physical inversion splits into spatial inversion of the temporal
integral, with both physical normalizations retained. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalInverseSchwartz_eq_temporalIntegral (f : SchwartzMap E V)
    (s : ℝ) (y : Euclidean d) :
    physicalInverseSchwartz f (timeSpacePoint s y) =
      ((2 * Real.pi) ^ d : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • physicalTemporalIntegral f s η := by
  rw [physicalInverseSchwartz_eq_integral]
  have hi : Integrable (fun ξ : E ↦
      Complex.exp (Complex.I * (inner ℝ (timeSpacePoint s y) ξ : ℂ)) • f ξ) := by
    apply f.integrable.norm.mono'
    · exact (by fun_prop : Continuous (fun ξ : E ↦
        Complex.exp (Complex.I * (inner ℝ (timeSpacePoint s y) ξ : ℂ)) •
          f ξ)).aestronglyMeasurable
    · filter_upwards [] with ξ
      simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
        one_mul, le_refl]
  rw [integral_eq_space_time _ hi]
  simp only [inner_eq_time_add_spatial, timeSpacePoint_time,
    spatialPart_timeSpacePoint, Complex.ofReal_add, mul_add, Complex.exp_add,
    mul_smul, physicalTemporalIntegral]
  simp_rw [smul_comm (Complex.exp (Complex.I * ((s * _ : ℝ) : ℂ))), integral_smul,
    smul_comm _ ((2 * Real.pi : ℂ)⁻¹), integral_smul, smul_smul]
  congr 1
  rw [pow_succ, mul_inv_rev]
  exact mul_comm _ _

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
