module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.MeanInequalities
/-!
# Fourier Sobolev interpolation and the weighted Young estimate

This proves the Fourier interpolation used after
`app:ch_regular_base:eq:graph-derivative-transfer` to obtain
`app:ch_regular_base:eq:fio-input`. Hölder is applied to the squared norms of
actual weighted Fourier representatives, with exponents `1 - k / s` and `k / s`.
The lower-order membership is the shared `MemFourierSobolev.mono` theorem;
both sides are proved finite before passing from `ℝ≥0∞` to `ℝ`.

The endpoint exponents are included. The case `s = 0` is handled separately,
and the weighted estimate allows `H = 0` and zero data.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal
namespace JanetCartan.Pseudodifferential
variable {d : ℕ}

/-- Pointwise geometric interpolation of the Fourier representatives used after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
private theorem norm_weightedL2Fourier_interpolate (s θ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖weightedL2Fourier (θ * s) u ξ‖ =
      ‖weightedL2Fourier 0 u ξ‖ ^ (1 - θ) * ‖weightedL2Fourier s u ξ‖ ^ θ := by
  simp only [norm_weightedL2Fourier, euclideanSobolevWeight_zero, one_mul]
  rw [Real.mul_rpow (le_of_lt (euclideanSobolevWeight_pos s ξ)) (norm_nonneg _)]
  have hw : euclideanSobolevWeight (θ * s) ξ = euclideanSobolevWeight s ξ ^ θ := by
    simp only [euclideanSobolevWeight, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring
  rw [hw, mul_left_comm, ← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_nonneg.mpr hθ') hθ]
  simp

/-- Extended-norm version of the pointwise interpolation after
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
private theorem enorm_weightedL2Fourier_interpolate (s θ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖weightedL2Fourier (θ * s) u ξ‖ₑ =
      ‖weightedL2Fourier 0 u ξ‖ₑ ^ (1 - θ) * ‖weightedL2Fourier s u ξ‖ₑ ^ θ := by
  simp only [← ofReal_norm]
  rw [norm_weightedL2Fourier_interpolate s θ hθ hθ', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (sub_nonneg.mpr hθ'),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hθ]

/-- Integral Hölder gives the extended-valued interpolation estimate after
`app:ch_regular_base:eq:graph-derivative-transfer`, including both endpoints. -/
private theorem eLpNorm_weightedL2Fourier_interpolate (s θ : ℝ)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    eLpNorm (weightedL2Fourier (θ * s) u) 2 volume ≤
      eLpNorm (weightedL2Fourier 0 u) 2 volume ^ (1 - θ) *
      eLpNorm (weightedL2Fourier s u) 2 volume ^ θ := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (aestronglyMeasurable_weightedL2Fourier _ u),
    ENNReal.toReal_ofNat]
  have hp (ξ : EuclideanSpace ℝ (Fin d)) :
      ‖weightedL2Fourier (θ * s) u ξ‖ₑ ^ (2 : ℝ) =
      (‖weightedL2Fourier 0 u ξ‖ₑ ^ (2 : ℝ)) ^ (1 - θ) *
      (‖weightedL2Fourier s u ξ‖ₑ ^ (2 : ℝ)) ^ θ := by
    rw [enorm_weightedL2Fourier_interpolate s θ hθ hθ',
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    simp only [← ENNReal.rpow_mul]
    congr 1 <;> congr 1 <;> ring
  simp_rw [hp]
  calc
    _ ≤ ((∫⁻ ξ, ‖weightedL2Fourier 0 u ξ‖ₑ ^ (2 : ℝ)) ^ (1 - θ) *
          (∫⁻ ξ, ‖weightedL2Fourier s u ξ‖ₑ ^ (2 : ℝ)) ^ θ) ^ (1 / (2 : ℝ)) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact ENNReal.lintegral_mul_norm_pow_le
        ((aestronglyMeasurable_weightedL2Fourier 0 u).enorm.pow_const _)
        ((aestronglyMeasurable_weightedL2Fourier s u).enorm.pow_const _)
        (sub_nonneg.mpr hθ') hθ (by ring)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      simp only [← ENNReal.rpow_mul]
      congr 1 <;> congr 1 <;> ring

/-- Fourier Sobolev interpolation after
`app:ch_regular_base:eq:graph-derivative-transfer`. Membership at the upper
order supplies lower-order membership through `MemFourierSobolev.mono` and
ensures finiteness before conversion to real norms. The cases `s = 0`, `k = 0`,
`k = s`, and zero data are included. -/
theorem fourierSobolevNorm_interpolate {s k : ℝ} (hk : 0 ≤ k) (hks : k ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev s u) :
    fourierSobolevNorm k u ≤
      fourierSobolevNorm 0 u ^ (1 - k / s) * fourierSobolevNorm s u ^ (k / s) := by
  by_cases hs : s = 0
  · have hk0 : k = 0 := le_antisymm (by simpa [hs] using hks) hk
    simp [hk0, hs]
  have hspos : 0 < s := lt_of_le_of_ne (hk.trans hks) (Ne.symm hs)
  have hθ : 0 ≤ k / s := div_nonneg hk hspos.le
  have hθ' : k / s ≤ 1 := (div_le_one hspos).mpr hks
  have he := eLpNorm_weightedL2Fourier_interpolate s (k / s) hθ hθ' u
  rw [div_mul_cancel₀ k hs] at he
  have hfinite : eLpNorm (weightedL2Fourier 0 u) 2 volume ^ (1 - k / s) *
      eLpNorm (weightedL2Fourier s u) 2 volume ^ (k / s) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hθ')
        (memFourierSobolev_zero u).eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hθ hu.eLpNorm_ne_top)
  have hkfinite := (hu.mono hks).eLpNorm_ne_top
  have hre := (ENNReal.toReal_le_toReal hkfinite hfinite).mpr he
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, fourierSobolevNorm] using hre

/-- The weighted Fourier interpolation and Young estimate used to deduce
`app:ch_regular_base:eq:fio-input` after
`app:ch_regular_base:eq:graph-derivative-transfer`. This includes `H = 0`
and all interpolation endpoints. -/
theorem fourierSobolevNorm_weighted_interpolate {s k H : ℝ}
    (hk : 0 ≤ k) (hks : k ≤ s) (hH : 0 ≤ H)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} (hu : MemFourierSobolev s u) :
    H ^ (1 - k / s) * fourierSobolevNorm k u ≤
      H * fourierSobolevNorm 0 u + fourierSobolevNorm s u := by
  have hθ : 0 ≤ k / s := div_nonneg hk (hk.trans hks)
  have hθ' : k / s ≤ 1 := by
    by_cases hs : s = 0
    · simp [hs]
    exact (div_le_one (lt_of_le_of_ne (hk.trans hks) (Ne.symm hs))).mpr hks
  have hzero := fourierSobolevNorm_nonneg 0 u
  have hhigh := fourierSobolevNorm_nonneg s u
  calc
    _ ≤ H ^ (1 - k / s) *
        (fourierSobolevNorm 0 u ^ (1 - k / s) * fourierSobolevNorm s u ^ (k / s)) :=
      mul_le_mul_of_nonneg_left (fourierSobolevNorm_interpolate hk hks hu)
        (Real.rpow_nonneg hH _)
    _ = (H * fourierSobolevNorm 0 u) ^ (1 - k / s) *
        fourierSobolevNorm s u ^ (k / s) := by
      rw [Real.mul_rpow hH hzero, mul_assoc]
    _ ≤ (1 - k / s) * (H * fourierSobolevNorm 0 u) +
        (k / s) * fourierSobolevNorm s u :=
      Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hθ') hθ
        (mul_nonneg hH hzero) hhigh (by ring)
    _ ≤ _ := by
      nlinarith [mul_nonneg hθ (mul_nonneg hH hzero),
        mul_nonneg (sub_nonneg.mpr hθ') hhigh]

end JanetCartan.Pseudodifferential
