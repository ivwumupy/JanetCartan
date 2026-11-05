module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Estimates
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Quantitative Euclidean raw synthesis

Cauchy–Schwarz in the Hilbert sum and the geometric sum of annular radii give
`app:ch_waves:eq:B-bounds`. No canonical-adjoint factor occurs here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.RawInputRealization

variable {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- Cauchy–Schwarz over the actual annular Hilbert sum
(`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_le {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i η, ‖β i η‖ ≤ M) (v : Input n radius) :
    (∫ η, ‖density β v η‖) ≤
      Real.sqrt (∑ i, (Real.sqrt (radius i) * M *
        Real.sqrt ((annularMeasure n (radius i) Set.univ).toReal)) ^ 2) * ‖v‖ := by
  let c : ι → ℝ := fun i ↦ Real.sqrt (radius i) * M *
    Real.sqrt ((annularMeasure n (radius i) Set.univ).toReal)
  have hcs : (∑ i, c i * ‖v i‖) ≤ Real.sqrt (∑ i, c i ^ 2) * ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [norm_input_sq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    _ ≤ ∫ η, ∑ i, ‖channelDensity (β i) (v i) η‖ := by
      apply integral_mono (integrable_density hβ hM v).norm
        (integrable_finsetSum _ (fun i _ ↦ (integrable_channelDensity (hβ i) (hM i) (v i)).norm))
      intro η
      exact norm_sum_le _ _
    _ = ∑ i, ∫ η, ‖channelDensity (β i) (v i) η‖ :=
      integral_finsetSum _ (fun i _ ↦ (integrable_channelDensity (hβ i) (hM i) (v i)).norm)
    _ ≤ ∑ i, c i * ‖v i‖ :=
      Finset.sum_le_sum (fun i _ ↦ integral_norm_channelDensity_le hM0 (hM i) (v i))
    _ ≤ _ := hcs

/-- Lebesgue volume of the unit ball in the initial dimension, used only as a
fixed dimension-dependent constant (`app:ch_waves:eq:B-bounds`). -/
def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Euclidean (n - 1)) 1)).toReal

/-- The annular volume has the initial-dimension exponent `n-1`
(`app:ch_waves:eq:B-bounds`). -/
theorem annularMeasure_real_le {R : ℝ} (hR : 0 ≤ R) :
    (annularMeasure n R Set.univ).toReal ≤ R ^ (n - 1) * unitBallVolume n := by
  have h := ENNReal.toReal_mono (measure_closedBall_lt_top (μ := volume)).ne
    (measure_mono (Set.sdiff_subset : annulus n R ⊆ Metric.closedBall 0 R))
  have he := Measure.addHaar_real_closedBall' (volume : Measure (Euclidean (n - 1))) 0 hR
  simp only [measureReal_def, finrank_euclideanSpace, Fintype.card_fin] at he
  rw [he] at h
  simpa only [annularMeasure, Measure.restrict_apply_univ, unitBallVolume, annulus] using h


/-- The squared per-band constant costs `R^n`, including the half-derivative
(`app:ch_waves:eq:B-bounds`). -/
theorem channel_constant_sq_le (hn : 1 ≤ n) {R M : ℝ} (hR : 0 ≤ R) :
    (Real.sqrt R * M * Real.sqrt ((annularMeasure n R Set.univ).toReal)) ^ 2 ≤
      M ^ 2 * unitBallVolume n * R ^ n := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hR, Real.sq_sqrt ENNReal.toReal_nonneg]
  calc
    _ ≤ R * M ^ 2 * (R ^ (n - 1) * unitBallVolume n) :=
      mul_le_mul_of_nonneg_left (annularMeasure_real_le hR) (by positivity)
    _ = _ := by
      have he : R * R ^ (n - 1) = R ^ n := by
        rw [← pow_succ']; congr 1; omega
      calc
        _ = M ^ 2 * unitBallVolume n * (R * R ^ (n - 1)) := by ring
        _ = _ := by rw [he]

/-- Dyadic squared-power sum, independent of the number of annuli
(`app:ch_waves:eq:B-bounds`). -/
theorem sum_dyadic_radii_pow_le (hn : 1 ≤ n) (J : ℕ) :
    (∑ i : Fin J, ((2 : ℝ) ^ i.val) ^ n) ≤ ((2 : ℝ) ^ J) ^ n := by
  have hn' : (2 : ℝ) ≤ 2 ^ n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  simp_rw [← pow_mul, Nat.mul_comm _ n, pow_mul]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc, pow_succ]
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) J]

/-- Fourier `L¹` bound at the dyadic ceiling, with exponent `n/2` and a
constant independent of `J` (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_density_dyadic_le (hn : 1 ≤ n) {J : ℕ}
    {β : Fin J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)) :
    (∫ η, ‖density β v η‖) ≤
      (M * Real.sqrt (unitBallVolume n)) * ((2 : ℝ) ^ J) ^ ((n : ℝ) / 2) * ‖v‖ := by
  have hs : (∑ i : Fin J, (Real.sqrt ((2 : ℝ) ^ i.val) * M *
      Real.sqrt ((annularMeasure n ((2 : ℝ) ^ i.val) Set.univ).toReal)) ^ 2) ≤
      M ^ 2 * unitBallVolume n * ((2 : ℝ) ^ J) ^ n := by
    calc
      _ ≤ ∑ i : Fin J, M ^ 2 * unitBallVolume n * ((2 : ℝ) ^ i.val) ^ n :=
        Finset.sum_le_sum (fun i _ ↦ channel_constant_sq_le hn (by positivity))
      _ = M ^ 2 * unitBallVolume n * ∑ i : Fin J, ((2 : ℝ) ^ i.val) ^ n :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dyadic_radii_pow_le hn J)
        (mul_nonneg (sq_nonneg M) ENNReal.toReal_nonneg)
  have he : Real.sqrt (M ^ 2 * unitBallVolume n * ((2 : ℝ) ^ J) ^ n) =
      (M * Real.sqrt (unitBallVolume n)) * ((2 : ℝ) ^ J) ^ ((n : ℝ) / 2) := by
    have hV : 0 ≤ unitBallVolume n := ENNReal.toReal_nonneg
    rw [Real.sqrt_mul (mul_nonneg (sq_nonneg M) hV),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM0, Real.sqrt_eq_rpow (((2 : ℝ) ^ J) ^ n),
      ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2 ^ J)]
    congr 2
    ring
  exact (integral_norm_density_le hβ hM0 hM v).trans
    ((mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs) (norm_nonneg _)).trans_eq
      (congrArg (fun t ↦ t * ‖v‖) he))

end JanetCartan.RawInputRealization
