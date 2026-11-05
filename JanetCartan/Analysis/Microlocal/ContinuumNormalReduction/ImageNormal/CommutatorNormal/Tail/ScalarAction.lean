module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.KernelSmoothness

/-!
# Exact Schwartz action of the intermediate tail kernel

Absolute integrability on the product Euclidean space justifies Fubini in
`app:ch_background:prop:bg-frame`, Step 1. Both Bessel factors are the actual
heat-integral kernels, and the intermediate factor is the full `1-β`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- Absolute convergence of the genuine double integral against a Schwartz
test, including the noncompact intermediate variable
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrable_imageCommutatorTail_double
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (u : S) (x : E) :
    Integrable (fun p : E × E ↦ (imageCommutatorTailSection χ β (x, p.1) : ℂ) *
      (imageBesselKernel (p.1 - p.2) : ℂ) * u p.2) (volume.prod volume) := by
  let f : E × E → ℂ := fun p ↦ (imageCommutatorTailSection χ β (x, p.1) : ℂ) *
    (imageBesselKernel (p.1 - p.2) : ℂ) * u p.2
  have hm : AEStronglyMeasurable f (volume.prod volume) := by
    have h1 : Measurable (fun p : E × E ↦ (imageCommutatorTailSection χ β (x, p.1) : ℂ)) :=
      (Complex.continuous_ofReal.comp
        ((contDiff_imageCommutatorTailSection χ β hχ hβ hδ hplateau).continuous.comp
          (continuous_const.prodMk continuous_fst))).measurable
    have h2 : Measurable (fun p : E × E ↦ (imageBesselKernel (p.1 - p.2) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_imageBesselKernel.comp
        (measurable_fst.sub measurable_snd))
    exact ((h1.mul h2).mul (u.continuous.measurable.comp measurable_snd)).aestronglyMeasurable
  have hi (y : E) : Integrable (fun z ↦ f (z, y)) := by
    simpa only [f, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul] using
      ((integrable_imageCommutatorTailSection_mul_bessel χ β hχ hχc hβ hβc hδ hplateau x y).ofReal.mul_const (u y))
  obtain ⟨C, hC, bC⟩ := exists_bound_imageCommutatorTailSection χ β hχ.continuous hχc
    hβ.continuous hβc hδ hplateau
  have hb (y : E) : (∫ z, ‖f (z, y)‖) ≤ C * ‖u y‖ := by
    calc
      _ ≤ ∫ z : E, C * imageBesselKernel (z - y) * ‖u y‖ := by
        apply integral_mono (hi y).norm
          (((integrable_imageBesselKernel.comp_sub_right y).const_mul C).mul_const ‖u y‖)
        intro z
        simp only [f, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (imageBesselKernel_nonneg (z - y))]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (bC (x, z)) (imageBesselKernel_nonneg (z - y)))
          (norm_nonneg _)
      _ = C * ‖u y‖ := by
        rw [integral_mul_const, integral_const_mul, integral_sub_right_eq_self,
          integral_imageBesselKernel, mul_one]
  apply (integrable_prod_iff' hm).mpr
  refine ⟨ae_of_all _ hi, ?_⟩
  apply (u.integrable.norm.const_mul C).mono' hm.norm.prod_swap.integral_prod_right'
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z ↦ norm_nonneg _)]
  exact hb y

/-- Fubini for the actual two Bessel factors; the iterated integral on the
right is precisely the original Schwartz composition
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_imageCommutatorTailKernel_mul_schwartz
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (u : S) (x : E) :
    (∫ y, (imageCommutatorTailKernel χ β (x, y) : ℂ) * u y) =
      ∫ z, (imageCommutatorTailSection χ β (x, z) : ℂ) * imageBesselSchwartzCLM u z := by
  simp_rw [imageCommutatorTailKernel, ← integral_complex_ofReal, ← integral_mul_const, Complex.ofReal_mul]
  rw [← integral_integral_swap (integrable_imageCommutatorTail_double
    χ β hχ hχc hβ hβc hδ hplateau u x)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [imageBesselSchwartzCLM_apply, imageBesselMultiplier_eq_convolution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [mul_assoc]

/-- The scalar kernel integrates the exact `χ² J (1-β) J` Schwartz tail,
with no compact replacement of `1-β`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageCommutatorTailKernel_schwartz_action
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (u : S) (x : E) :
    SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y) ^ 2 : ℂ))
      (imageBesselSchwartzCLM (imageBesselSchwartzCLM u -
        SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) (imageBesselSchwartzCLM u))) x =
      ∫ y, (imageCommutatorTailKernel χ β (x, y) : ℂ) * u y := by
  have hχt := hχc.hasTemperateGrowth hχ
  have hβt := hβc.hasTemperateGrowth hβ
  have hsq : (fun y ↦ ((χ y) ^ 2 : ℂ)).HasTemperateGrowth := by fun_prop
  have hb : (fun y ↦ (β y : ℂ)).HasTemperateGrowth := by fun_prop
  rw [integral_imageCommutatorTailKernel_mul_schwartz χ β hχ hχc hβ hβc hδ hplateau,
    SchwartzMap.smulLeftCLM_apply_apply hsq, imageBesselSchwartzCLM_apply,
    imageBesselMultiplier_eq_convolution]
  simp only [smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [sub_apply, SchwartzMap.smulLeftCLM_apply_apply hb, smul_eq_mul,
    imageCommutatorTailSection, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

/-- Insertion of the compact source cutoff is exact for tests supported
in its plateau. This is applied to the actual source factor `P* μ`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageCommutatorTailKernel_schwartz_action
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1)
    (u : S) (hu : ∀ y, u y ≠ 0 → β y = 1) (x : E) :
    SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y) ^ 2 : ℂ))
      (imageBesselSchwartzCLM (imageBesselSchwartzCLM u -
        SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) (imageBesselSchwartzCLM u))) x =
      ∫ y, (localizedImageCommutatorTailKernel χ β (x, y) : ℂ) * u y := by
  rw [imageCommutatorTailKernel_schwartz_action χ β hχ hχc hβ hβc hδ hplateau]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : u y = 0
  · simp [hy]
  · simp [localizedImageCommutatorTailKernel, hu y hy]

end JanetCartan.ContinuumNormalReduction.ImageNormal
