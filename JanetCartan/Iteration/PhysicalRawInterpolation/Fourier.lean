module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.InputScale
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Interpolation.Sobolev

/-!
# Weighted endpoint interpolation on the actual original Fourier inputs

For `app:ch_background:prop:bg-adjoint`, the current-minus-reference raw
input is controlled at a fixed high order before its L² difference is made
small. These estimates retain the full initial Fourier weight, including all
three carrier variables and the unitary `2π` normalization. The auxiliary
periodic slots use their original Fourier series and Haar measure.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators ENNReal

namespace JanetCartan.PhysicalRawInterpolation

open ContinuumRow CarrierSobolev PeriodicSobolevSpace

private theorem pow_le_scaled_endpoints {b K : ℝ} (hb : 0 ≤ b) (hK : 1 ≤ K) (s : ℕ) :
    b ^ s ≤ K ^ s + K⁻¹ * b ^ (s + 1) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  by_cases h : b ≤ K
  · exact (pow_le_pow_left₀ hb h s).trans (le_add_of_nonneg_right (by positivity))
  · have h1 : 1 ≤ K⁻¹ * b := by
      have hp := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (inv_nonneg.mpr hKpos.le)
      simpa only [inv_mul_cancel₀ hKpos.ne'] using hp
    apply le_trans (b := K⁻¹ * b ^ (s + 1))
    · calc
        b ^ s = b ^ s * 1 := (mul_one _).symm
        _ ≤ b ^ s * (K⁻¹ * b) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hb s)
        _ = _ := by rw [pow_succ]; ring
    · exact le_add_of_nonneg_left (by positivity)

/-- Literal full initial-weight endpoint inequality, with no loss in the
carrier variables or change of Fourier normalization. -/
theorem initialWeight_le_scaled_endpoints {n : ℕ} (s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (ξ : CarrierVariable n) :
    initialWeight s ξ ≤ K ^ s + K⁻¹ * initialWeight (s + 1) ξ := by
  let b : ℝ := 1 + (2 * Real.pi) ^ 2 * ‖initialCoordinates n ξ‖ ^ 2
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have he (j : ℕ) : initialWeight j ξ = (b ^ (1 / 2 : ℝ)) ^ j := by
    change b ^ ((j : ℝ) / 2) = (b ^ (1 / 2 : ℝ)) ^ j
    rw [← Real.rpow_mul_natCast hb]
    congr 1
    ring
  rw [he s, he (s + 1)]
  exact pow_le_scaled_endpoints (Real.rpow_nonneg hb _) hK s

/-- Actual physical full-initial Fourier interpolation. Membership is the
original finite-energy domain, not a bound or an assumed interpolation field. -/
theorem physicalSobolevNorm_le_scaled_endpoints {n : ℕ} (s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (f : CarrierL2 n) (hf : MemPhysicalSobolev (s + 1) f) :
    physicalSobolevNorm s f ≤ K ^ s * ‖f‖ + K⁻¹ * physicalSobolevNorm (s + 1) f := by
  let a := physicalSobolevAnalysis s ⟨f, hf.mono (Nat.le_succ s)⟩
  let z := initialFourier n f
  let b := physicalSobolevAnalysis (s + 1) ⟨f, hf⟩
  have hpoint : ‖a‖ ≤ ‖K ^ s • z + K⁻¹ • b‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.memLp _).eLpNorm_ne_top
    apply eLpNorm_mono_ae (Lp.memLp a).aestronglyMeasurable
    filter_upwards [physicalSobolevAnalysis_coeFn s ⟨f, hf.mono (Nat.le_succ s)⟩,
      physicalSobolevAnalysis_coeFn (s + 1) ⟨f, hf⟩,
      Lp.coeFn_add (K ^ s • z) (K⁻¹ • b), Lp.coeFn_smul (K ^ s) z,
      Lp.coeFn_smul K⁻¹ b] with ξ ha hb hab hz hk
    change a ξ = initialWeight s ξ • z ξ at ha
    change b ξ = initialWeight (s + 1) ξ • z ξ at hb
    simp only [ha, hab, Pi.add_apply, hz, hk, Pi.smul_apply, hb]
    change ‖initialWeight s ξ • z ξ‖ ≤ ‖K ^ s • z ξ + K⁻¹ • initialWeight (s + 1) ξ • z ξ‖
    have hweight := initialWeight_pos (s + 1) ξ
    rw [smul_smul, ← add_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (initialWeight_pos _ _), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (initialWeight_le_scaled_endpoints s hK ξ) (norm_nonneg _)
  have hb := hpoint.trans (norm_add_le (K ^ s • z) (K⁻¹ • b))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ K ^ s), abs_of_nonneg (by positivity : 0 ≤ K⁻¹)] at hb
  simpa only [a, b, z, norm_physicalSobolevAnalysis, initialFourier_norm] using hb

/-- The same endpoint bound on the ACTUAL raw `(z,η)` input. Its norm is the
full initial Sobolev norm after the original partial unitary inverse, not an
η-only multiplier norm (`app:ch_background:prop:bg-adjoint`). -/
theorem rawSobolevNorm_le_scaled_endpoints {n : ℕ} (s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (f : CarrierL2 n) (hf : MemRawSobolev (s + 1) f) :
    rawSobolevNorm s f ≤ K ^ s * ‖f‖ + K⁻¹ * rawSobolevNorm (s + 1) f := by
  simpa only [rawSobolevNorm, LinearIsometryEquiv.norm_map] using
    physicalSobolevNorm_le_scaled_endpoints s hK (partialUnitaryInverse n f) hf

/-- The two genuine periodic auxiliary components have exactly the same
endpoint interpolation, retaining their original Fourier sequence. -/
theorem periodicSobolevNorm_le_scaled_endpoints {n : ℕ} (s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (u : PeriodicL2 n (Euclidean n)) (hu : u ∈ periodicSobolevLevel n (Euclidean n) (s + 1)) :
    periodicSobolevNorm s u ≤ K ^ s * ‖u‖ + K⁻¹ * periodicSobolevNorm (s + 1) u := by
  let a := periodicSobolevAnalysis s ⟨u, antitone_periodicSobolevLevel (Nat.le_succ s) hu⟩
  let z := periodicSobolevAnalysis 0 ⟨u, antitone_periodicSobolevLevel (Nat.zero_le _) hu⟩
  let b := periodicSobolevAnalysis (s + 1) ⟨u, hu⟩
  have hpoint : ‖a‖ ≤ ‖K ^ s • z + K⁻¹ • b‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro k
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, a, z, b,
      periodicSobolevAnalysis_apply, weightedPeriodicL2FourierCoeff_apply,
      periodicSobolevWeight, pow_zero, one_smul]
    rw [smul_smul, ← add_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_scaled_endpoints (Real.sqrt_nonneg _) hK s) (norm_nonneg _)
  have hb := hpoint.trans (norm_add_le (K ^ s • z) (K⁻¹ • b))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ K ^ s), abs_of_nonneg (by positivity : 0 ≤ K⁻¹)] at hb
  have hz : ‖z‖ = ‖u‖ := periodicSobolevSeminorm_zero _
  have ha : ‖a‖ = periodicSobolevNorm s u := periodicSobolevSeminorm_eq _ _
  have ht : ‖b‖ = periodicSobolevNorm (s + 1) u := by
    change periodicSobolevSeminorm (s + 1) ⟨u, hu⟩ = _
    rw [periodicSobolevSeminorm_eq]
    simp only [Nat.cast_add, Nat.cast_one]
  simpa only [hz, ha, ht] using hb

end JanetCartan.PhysicalRawInterpolation
