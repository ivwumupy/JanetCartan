module
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.KernelDefinitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
/-!
# Mass and integrability of the image Bessel heat integral

For `app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-frame`,
Step 1, the explicit heat density has mass one. Fubini and the Gamma integral
then prove absolute convergence almost everywhere and unit Lebesgue mass of
`imageBesselKernel`. These are the integrability inputs for its Fourier identity
and for the local comparison's lattice periodization.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positivity of the heat density at nonnegative times (`app:ch_background:defn:bg-row`). -/
theorem imageBesselHeatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : 0 ≤ imageBesselHeatKernel t x := by
  unfold imageBesselHeatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

/-- Every positive-time heat density is Lebesgue integrable (`app:ch_background:defn:bg-row`). -/
theorem integrable_imageBesselHeatKernel {t : ℝ} (ht : 0 < t) : Integrable (imageBesselHeatKernel (d := d) t) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := ((4 * t)⁻¹ : ℝ)) (by simp; positivity) 0 0).re
  have he : (fun x : E ↦ Real.exp (-(‖x‖ ^ 2) / (4 * t))) =
      (fun x : E ↦ (Complex.exp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖x‖ ^ 2 + 0 * inner ℝ (0 : E) x)).re) := by
    ext x
    simp only [zero_mul, add_zero]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.exp_ofReal_re]
    congr 1
    ring
  exact (he ▸ h).const_mul _

/-- The heat density has unit mass, with the exact normalization of
`app:ch_background:defn:bg-row`. -/
theorem integral_imageBesselHeatKernel {t : ℝ} (ht : 0 < t) : (∫ x : E, imageBesselHeatKernel t x) = 1 := by
  have he : (fun x : E ↦ Real.exp (-(‖x‖ ^ 2) / (4 * t))) =
      (fun x : E ↦ Real.exp (-((4 * t)⁻¹) * ‖x‖ ^ 2)) := by
    ext x
    congr 1
    ring
  simp only [imageBesselHeatKernel, integral_const_mul, he]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    finrank_euclideanSpace_fin]
  have hbase : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by rw [div_inv_eq_mul]; ring
  rw [hbase, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    ← Real.rpow_add (by positivity)]
  simp

/-- Joint measurability for the Fubini step in the kernel realization
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem measurable_imageBesselHeatKernel :
    Measurable (fun p : ℝ × E ↦ imageBesselHeatKernel p.1 p.2) := by
  unfold imageBesselHeatKernel
  fun_prop

/-- The half-order Gamma weight is integrable, as needed for the Bessel
heat integral in `app:ch_background:defn:bg-row`. -/
theorem integrable_imageBesselHeatWeight :
    IntegrableOn (fun t : ℝ ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t)) (Ioi 0) := by
  simpa only [show (1 : ℝ) / 2 - 1 = -(1 : ℝ) / 2 by norm_num, mul_comm]
    using Real.GammaIntegral_convergent (by norm_num : 0 < (1 : ℝ) / 2)

/-- The weight has mass `√π`; the Bessel kernel divides by this same
constant (`app:ch_background:defn:bg-row`). -/
theorem integral_imageBesselHeatWeight :
    (∫ t : ℝ in Ioi 0, t ^ (-(1 : ℝ) / 2) * Real.exp (-t)) = Real.sqrt Real.pi := by
  simpa only [show (1 : ℝ) / 2 - 1 = -(1 : ℝ) / 2 by norm_num, one_mul,
    div_one, Real.one_rpow, Real.Gamma_one_half_eq]
    using Real.integral_rpow_mul_exp_neg_mul_Ioi
      (by norm_num : 0 < (1 : ℝ) / 2) (by norm_num : 0 < (1 : ℝ))

/-- Joint absolute integrability of the actual heat integrand; this
justifies the later Fourier/Fubini interchange in `app:ch_background:prop:bg-frame`. -/
theorem integrable_imageBesselHeatIntegrand :
    Integrable (fun p : ℝ × E ↦ p.1 ^ (-(1 : ℝ) / 2) * Real.exp (-p.1) *
      imageBesselHeatKernel p.1 p.2) ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : Measurable (fun p : ℝ × E ↦ p.1 ^ (-(1 : ℝ) / 2) * Real.exp (-p.1) *
      imageBesselHeatKernel p.1 p.2) := by
    exact (Measurable.mul (by fun_prop) (by fun_prop)).mul measurable_imageBesselHeatKernel
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrable_imageBesselHeatKernel ht).const_mul _
  · apply integrable_imageBesselHeatWeight.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn : ∀ x : E, 0 ≤ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) *
        imageBesselHeatKernel t x := fun x ↦
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (imageBesselHeatKernel_nonneg ht.le x)
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    rw [integral_const_mul, integral_imageBesselHeatKernel ht, mul_one]

/-- The defining heat integral converges absolutely almost everywhere
in Euclidean space (`app:ch_background:defn:bg-row`). -/
theorem ae_integrable_imageBesselHeatIntegrand :
    ∀ᵐ x : E, IntegrableOn (fun t : ℝ ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) *
      imageBesselHeatKernel t x) (Ioi 0) :=
  integrable_imageBesselHeatIntegrand.prod_left_ae

/-- The literal image Bessel kernel is Lebesgue integrable
(`app:ch_background:prop:bg-frame`, Step 1), the input to lattice periodization. -/
theorem integrable_imageBesselKernel : Integrable (imageBesselKernel (d := d)) :=
  integrable_imageBesselHeatIntegrand.integral_prod_right.const_mul _

/-- The totalized Bessel heat integral is nonnegative everywhere
(`app:ch_background:defn:bg-row`). -/
theorem imageBesselKernel_nonneg (x : E) : 0 ≤ imageBesselKernel x := by
  apply mul_nonneg (by positivity)
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        (imageBesselHeatKernel_nonneg ht.le x)

/-- The actual image Bessel kernel has unit Lebesgue mass
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_imageBesselKernel : (∫ x : E, imageBesselKernel x) = 1 := by
  unfold imageBesselKernel
  rw [integral_const_mul, ← integral_integral_swap integrable_imageBesselHeatIntegrand]
  have he : (∫ t : ℝ in Ioi 0, ∫ x : E,
      t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x) =
      ∫ t : ℝ in Ioi 0, t ^ (-(1 : ℝ) / 2) * Real.exp (-t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [integral_const_mul, integral_imageBesselHeatKernel ht, mul_one]
  rw [he, integral_imageBesselHeatWeight, inv_mul_cancel₀ (by positivity)]

end JanetCartan.ContinuumNormalReduction.ImageNormal
