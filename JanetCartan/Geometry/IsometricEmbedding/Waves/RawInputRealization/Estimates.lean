module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Spaces

/-!
# Integrability and Fourier synthesis on Lebesgue annuli

The inputs below are measurable masks with a uniform pointwise bound. They are
inputs to the deduction of `app:ch_waves:eq:B-bounds`, not assumed synthesis
estimates. The annular data are arbitrary elements of the actual `L²` spaces.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.RawInputRealization

variable {n : ℕ} {R : ℝ}

/-- Finite-measure Cauchy–Schwarz for an actual annular datum
(`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_annularL2_le (v : AnnularL2 n R) :
    (∫ η, ‖v η‖ ∂annularMeasure n R) ≤
      ‖v‖ * Real.sqrt ((annularMeasure n R Set.univ).toReal) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable v)
  have ht : eLpNorm v 2 (annularMeasure n R) *
      (annularMeasure n R Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (Lp.eLpNorm_ne_top v)
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono ht h
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable v),
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable v),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] at h'
  norm_num [Real.sqrt_eq_rpow] at h' ⊢
  exact h'

/-- A measurable annular mask gives a measurable density
(`app:ch_waves:thm:individual`). -/
theorem aestronglyMeasurable_channelDensity {β : Euclidean (n - 1) → ℂ}
    (hβ : Measurable β) (v : AnnularL2 n R) :
    AEStronglyMeasurable (channelDensity β v) volume := by
  apply (aestronglyMeasurable_indicator_iff (measurableSet_annulus n R)).mpr
  exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).aestronglyMeasurable.mul hβ.aestronglyMeasurable).mul (Lp.aestronglyMeasurable v)

private theorem channel_bound {β : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hβ : ∀ η, ‖β η‖ ≤ M) (v : AnnularL2 n R) {η : Euclidean (n - 1)}
    (hη : η ∈ annulus n R) :
    ‖(Real.sqrt ‖η‖ : ℂ) * β η * v η‖ ≤ Real.sqrt R * M * ‖v η‖ := by
  have hR : ‖η‖ ≤ R := by simpa using hη.1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (Real.sqrt_le_sqrt hR) (hβ η) (norm_nonneg _) (Real.sqrt_nonneg _))
    (norm_nonneg _)

/-- Every bounded measurable masked annular datum is Fourier integrable
(`app:ch_waves:eq:B-bounds`). -/
theorem integrable_channelDensity {β : Euclidean (n - 1) → ℂ}
    (hβ : Measurable β) {M : ℝ} (hM : ∀ η, ‖β η‖ ≤ M) (v : AnnularL2 n R) :
    Integrable (channelDensity β v) volume := by
  apply (integrable_indicator_iff (measurableSet_annulus n R)).mpr
  apply ((MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp v)).norm.const_mul
    (Real.sqrt R * M)).mono'
  · exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).aestronglyMeasurable.mul hβ.aestronglyMeasurable).mul (Lp.aestronglyMeasurable v)
  · filter_upwards [ae_restrict_mem (measurableSet_annulus n R)] with η hη
    exact channel_bound hM v hη

/-- The single-annulus Fourier `L¹` bound from Cauchy–Schwarz, including exactly
one half-derivative (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_channelDensity_le {β : Euclidean (n - 1) → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ η, ‖β η‖ ≤ M)
    (v : AnnularL2 n R) :
    (∫ η, ‖channelDensity β v η‖) ≤
      (Real.sqrt R * M * Real.sqrt ((annularMeasure n R Set.univ).toReal)) * ‖v‖ := by
  have hv := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp v)
  calc
    _ = ∫ η, ‖(Real.sqrt ‖η‖ : ℂ) * β η * v η‖ ∂annularMeasure n R := by
      simp only [channelDensity, norm_indicator_eq_indicator_norm, integral_indicator
        (measurableSet_annulus n R), annularMeasure]
    _ ≤ ∫ η, (Real.sqrt R * M) * ‖v η‖ ∂annularMeasure n R := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (hv.norm.const_mul _)
      filter_upwards [ae_restrict_mem (measurableSet_annulus n R)] with η hη
      exact channel_bound hM v hη
    _ = (Real.sqrt R * M) * ∫ η, ‖v η‖ ∂annularMeasure n R := integral_const_mul _ _
    _ ≤ (Real.sqrt R * M) * (‖v‖ * Real.sqrt ((annularMeasure n R Set.univ).toReal)) :=
      mul_le_mul_of_nonneg_left (integral_norm_annularL2_le v) (mul_nonneg (Real.sqrt_nonneg _) hM0)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- Integrability of the literal finite density (`app:ch_waves:eq:B-bounds`). -/
theorem integrable_density {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n radius) : Integrable (density β v) volume :=
  integrable_finsetSum _ (fun i _ ↦ integrable_channelDensity (hβ i) (hM i) (v i))

/-- Every polynomial Fourier moment is integrable, with no regularity of the
`L²` input required (`app:ch_waves:thm:individual`). -/
theorem integrable_density_moment {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n radius) {K : ℝ} (_hK0 : 0 ≤ K) (hK : ∀ i, radius i ≤ K) (m : ℕ) :
    Integrable (fun η ↦ ‖η‖ ^ m * ‖density β v η‖) volume := by
  have hf := integrable_density hβ hM v
  apply (hf.norm.const_mul (K ^ m)).mono'
    ((continuous_norm.pow m).aestronglyMeasurable.mul hf.aestronglyMeasurable.norm)
  filter_upwards [] with η
  change ‖‖η‖ ^ m * ‖density β v η‖‖ ≤ K ^ m * ‖density β v η‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg η) m) (norm_nonneg _))]
  by_cases hη : ‖η‖ ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hη m) (norm_nonneg _)
  · rw [density_eq_zero_above_ceiling β v hK (lt_of_not_ge hη)]
    simp only [norm_zero, mul_zero, le_refl]

/-- Smoothness of the actual inverse Fourier field at every order
(`app:ch_waves:thm:individual`). -/
theorem contDiff_field {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v : Input n radius) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ i, radius i ≤ K) :
    ContDiff ℝ ∞ (field β v) :=
  VectorFourier.contDiff_fourierIntegral (radianPairing n)
    (fun m _ ↦ integrable_density_moment hβ hM v hK0 hK m)

end JanetCartan.RawInputRealization
