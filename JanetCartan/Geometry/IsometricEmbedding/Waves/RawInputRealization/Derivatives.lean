module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Linearity

/-!
# Initial derivatives in radian Fourier normalization

The bounds here concern the initial inverse Fourier field, before spatial cutoff,
as in `app:ch_waves:eq:B-bounds`. They do not assert physical slice Sobolev bounds
for the WKB map. The norm is the operator norm of the iterated Fréchet derivative.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawInputRealization

variable {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- Explicit radian inverse Fourier formula, with no hidden `2π` factor
(`app:ch_waves:thm:individual`). -/
theorem field_eq_integral_exp (β : ι → Euclidean (n - 1) → ℂ)
    (v : Input n radius) (x : Euclidean (n - 1)) :
    field β v x = ∫ η, Complex.exp ((inner ℝ η x : ℂ) * Complex.I) * density β v η := by
  rw [field, Real.vector_fourierIntegral_eq_integral_exp_smul]
  congr 1
  funext η
  have hp : -2 * Real.pi * (radianPairing n η x) = inner ℝ η x := by
    change -2 * Real.pi * (-(2 * Real.pi)⁻¹ * inner ℝ η x) = _
    field_simp
  change Complex.exp (↑(-2 * Real.pi * radianPairing n η x) * Complex.I) * _ = _
  rw [hp]

/-- Cancellation of Mathlib's `2π` by the radian pairing
(`app:ch_waves:eq:B-bounds`). -/
theorem radianPairing_norm_bound (n : ℕ) : 2 * Real.pi * ‖radianPairing n‖ ≤ 1 := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  calc
    _ ≤ 2 * Real.pi * (‖(-(2 * Real.pi)⁻¹ : ℝ)‖ *
        ‖innerSL ℝ (E := Euclidean (n - 1))‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_smul_le (-(2 * Real.pi)⁻¹ : ℝ) (innerSL ℝ (E := Euclidean (n - 1)))) hp.le
    _ = ‖innerSL ℝ (E := Euclidean (n - 1))‖ := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
      field_simp
    _ ≤ 1 := norm_innerSL_le ℝ

/-- Every initial derivative is bounded by its Fourier moment, with the exact
radian factor one (`app:ch_waves:eq:B-bounds`). -/
theorem norm_iteratedFDeriv_field_le_moment {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n radius) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, radius i ≤ K)
    (m : ℕ) (x : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (field β v) x‖ ≤ ∫ η, ‖η‖ ^ m * ‖density β v η‖ := by
  have hm := integrable_density_moment hβ hM v hK0 hK m
  rw [field, VectorFourier.iteratedFDeriv_fourierIntegral (N := ⊤) (radianPairing n)
    (fun j _ ↦ integrable_density_moment hβ hM v hK0 hK j)
    (integrable_density hβ hM v).aestronglyMeasurable (by simp)]
  apply (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hm
  filter_upwards [] with η
  have h := VectorFourier.norm_fourierPowSMulRight_le (radianPairing n) (density β v) η m
  calc
    _ ≤ (2 * Real.pi * ‖radianPairing n‖) ^ m * ‖η‖ ^ m * ‖density β v η‖ := h
    _ ≤ 1 ^ m * ‖η‖ ^ m * ‖density β v η‖ := by
      gcongr
      exact radianPairing_norm_bound n
    _ = _ := by simp

/-- Bernstein bound from compact input support, derived after integrability
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_iteratedFDeriv_field_le {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n radius) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, radius i ≤ K)
    (m : ℕ) (x : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (field β v) x‖ ≤ K ^ m * ∫ η, ‖density β v η‖ := by
  apply (norm_iteratedFDeriv_field_le_moment hβ hM v hK0 hK m x).trans
  rw [← integral_const_mul]
  apply integral_mono (integrable_density_moment hβ hM v hK0 hK m)
    ((integrable_density hβ hM v).norm.const_mul _)
  intro η
  change ‖η‖ ^ m * ‖density β v η‖ ≤ K ^ m * ‖density β v η‖
  by_cases hη : ‖η‖ ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hη m) (norm_nonneg _)
  · rw [density_eq_zero_above_ceiling β v hK (lt_of_not_ge hη)]
    simp

/-- The dyadic initial `C^m` estimate, pointwise at every derivative order,
with constants independent of the number of annuli (`app:ch_waves:eq:B-bounds`). -/
theorem norm_iteratedFDeriv_field_dyadic_le (hn : 1 ≤ n) {J : ℕ}
    {β : Fin J → Euclidean (n - 1) → ℂ} (hβ : ∀ i, Measurable (β i))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n (fun i : Fin J ↦ (2 : ℝ) ^ i.val)) (m : ℕ) (x : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (field β v) x‖ ≤
      (M * Real.sqrt (unitBallVolume n)) *
        ((2 : ℝ) ^ J) ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
  have hK : ∀ i : Fin J, (2 : ℝ) ^ i.val ≤ 2 ^ J :=
    fun i ↦ pow_le_pow_right₀ (by norm_num) i.isLt.le
  have h := (norm_iteratedFDeriv_field_le hβ hM v (by positivity) hK m x).trans
    (mul_le_mul_of_nonneg_left (integral_norm_density_dyadic_le hn hβ hM0 hM v) (by positivity))
  convert h using 1
  rw [Real.rpow_add (by positivity), Real.rpow_natCast]
  ring

end JanetCartan.RawInputRealization
