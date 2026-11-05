module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density.Fourier

/-!
# Comparison with the Euclidean Sobolev weight

The physical derivative weight contains `2π`. The bounds below transfer the
checked compact smooth approximation theorem to the actual physical norm in
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

/-- A uniform weight-comparison constant for compact smooth approximation in
`app:ch_background:prop:bg-adjoint`. -/
def densityWeightConstant (s : ℕ) : ℝ :=
  (1 + (2 * Real.pi) ^ 2) ^ ((s : ℝ) / 2)

/-- Positivity of the comparison constant (`app:ch_background:prop:bg-adjoint`). -/
theorem densityWeightConstant_pos (s : ℕ) : 0 < densityWeightConstant s := by
  unfold densityWeightConstant
  positivity

/-- The Euclidean Bessel weight is bounded by the physical derivative weight
(`app:ch_background:prop:bg-adjoint`). -/
theorem euclideanSobolevWeight_le_initialWeight (n s : ℕ) (ξ : CarrierVariable n) :
    euclideanSobolevWeight (s : ℝ) (densityCoordinates n ξ) ≤ initialWeight s ξ := by
  unfold euclideanSobolevWeight initialWeight
  rw [densityCoordinates_norm]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [sq_nonneg ‖initialCoordinates n ξ‖,
    mul_le_mul_of_nonneg_right hp (sq_nonneg ‖initialCoordinates n ξ‖)]

/-- Uniform reverse weight comparison, retaining the `2π` derivative
normalization in `app:ch_background:prop:bg-adjoint`. -/
theorem initialWeight_le_euclideanSobolevWeight (n s : ℕ) (ξ : CarrierVariable n) :
    initialWeight s ξ ≤ densityWeightConstant s *
      euclideanSobolevWeight (s : ℝ) (densityCoordinates n ξ) := by
  unfold euclideanSobolevWeight initialWeight densityWeightConstant
  rw [densityCoordinates_norm, ← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  nlinarith [sq_nonneg (2 * Real.pi), sq_nonneg ‖initialCoordinates n ξ‖]

set_option maxHeartbeats 800000 in
/-- Physical finite energy implies the Euclidean Fourier Sobolev membership
needed to invoke compact smooth density (`app:ch_background:prop:bg-adjoint`). -/
theorem MemPhysicalSobolev.memFourierSobolev_densityL2Equiv {n s : ℕ}
    {f : CarrierL2 n} (hf : MemPhysicalSobolev s f) :
    MemFourierSobolev (s : ℝ) (densityL2Equiv n f) := by
  let g := weightedL2Fourier (s : ℝ) (densityL2Equiv n f)
  have hg : AEStronglyMeasurable g volume := aestronglyMeasurable_weightedL2Fourier _ _
  have hm : MemLp (g ∘ densityCoordinates n) 2 (carrierMeasure n) := by
    apply MemLp.mono hf (hg.comp_measurePreserving (densityCoordinates_measurePreserving n))
    filter_upwards [initialFourier_coeFn_densityCoordinates n f] with ξ hξ
    change ‖weightedL2Fourier (s : ℝ) (densityL2Equiv n f) (densityCoordinates n ξ)‖ ≤ ‖initialWeight s ξ • initialFourier n f ξ‖
    rw [norm_weightedL2Fourier, norm_smul, Real.norm_eq_abs,
      abs_of_pos (initialWeight_pos _ _), hξ]
    exact mul_le_mul_of_nonneg_right (euclideanSobolevWeight_le_initialWeight n s ξ)
      (norm_nonneg _)
  have hm' := hm.comp_measurePreserving (densityCoordinates_symm_measurePreserving n)
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply,
    MemFourierSobolev, g] using hm'

/-- Euclidean finite Fourier energy implies actual physical finite energy;
no membership hypothesis is added to compact smooth functions
(`app:ch_background:prop:bg-adjoint`). -/
theorem memPhysicalSobolev_of_memFourierSobolev_densityL2Equiv {n s : ℕ}
    {f : CarrierL2 n} (hf : MemFourierSobolev (s : ℝ) (densityL2Equiv n f)) :
    MemPhysicalSobolev s f := by
  have hm := (hf.const_smul (densityWeightConstant s)).comp_measurePreserving
    (densityCoordinates_measurePreserving n)
  apply hm.mono (aestronglyMeasurable_weightedInitialFourier s f)
  filter_upwards [initialFourier_coeFn_densityCoordinates n f] with ξ hξ
  change ‖initialWeight s ξ • initialFourier n f ξ‖ ≤
    ‖densityWeightConstant s • weightedL2Fourier (s : ℝ)
      (densityL2Equiv n f) (densityCoordinates n ξ)‖
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _),
    abs_of_pos (densityWeightConstant_pos _), norm_weightedL2Fourier, hξ,
    Function.comp_apply]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (initialWeight_le_euclideanSobolevWeight n s ξ)
    (norm_nonneg _)

/-- Quantitative norm comparison transfers Euclidean approximation to the
actual physical Sobolev topology (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevNorm_le_fourierSobolevNorm {n s : ℕ} {f : CarrierL2 n}
    (hf : MemFourierSobolev (s : ℝ) (densityL2Equiv n f)) :
    physicalSobolevNorm s f ≤ densityWeightConstant s *
      fourierSobolevNorm (s : ℝ) (densityL2Equiv n f) := by
  let g := weightedL2Fourier (s : ℝ) (densityL2Equiv n f)
  have hm := (hf.const_smul (densityWeightConstant s)).comp_measurePreserving
    (densityCoordinates_measurePreserving n)
  have he : eLpNorm (fun ξ ↦ initialWeight s ξ • initialFourier n f ξ)
      2 (carrierMeasure n) ≤
      eLpNorm ((densityWeightConstant s • g) ∘ densityCoordinates n) 2 (carrierMeasure n) := by
    apply eLpNorm_mono_ae (aestronglyMeasurable_weightedInitialFourier s f)
    filter_upwards [initialFourier_coeFn_densityCoordinates n f] with ξ hξ
    change ‖initialWeight s ξ • initialFourier n f ξ‖ ≤
      ‖densityWeightConstant s • weightedL2Fourier (s : ℝ)
        (densityL2Equiv n f) (densityCoordinates n ξ)‖
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (initialWeight_pos _ _),
      abs_of_pos (densityWeightConstant_pos _), norm_weightedL2Fourier, hξ,
      Function.comp_apply]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (initialWeight_le_euclideanSobolevWeight n s ξ)
      (norm_nonneg _)
  have hr := ENNReal.toReal_mono hm.eLpNorm_ne_top he
  rw [eLpNorm_comp_measurePreserving
    (hf.aestronglyMeasurable.const_smul (densityWeightConstant s))
    (densityCoordinates_measurePreserving n), eLpNorm_const_smul,
    ENNReal.toReal_mul] at hr
  simpa only [physicalSobolevNorm, fourierSobolevNorm, g, ENNReal.coe_toReal,
    Real.norm_eq_abs, abs_of_pos (densityWeightConstant_pos _),
    coe_nnnorm, toReal_enorm] using hr

end JanetCartan.CarrierSobolev
