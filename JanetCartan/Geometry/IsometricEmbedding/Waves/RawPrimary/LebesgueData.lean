module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.MaskedEstimates

/-!
# Literal Lebesgue data for the raw primary construction

The data in `app:ch_waves:thm:individual` are the original smooth wide bands,
with the fixed detector/high-pass product `d`. We use the proved isometric
two-shell refinement only to establish integrability and moments. The resulting
initial field retains both complex quadratures and is multiplied by the spatial
initial cutoff only after Fourier synthesis. The support statements about the
density do not assert frequency support of that spatial product.

These are input constructions for the raw wave, not its physical slice estimate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary
open RawInputPartition RawInputRealization

variable {n J : ℕ} {d : Euclidean (n - 1) → ℂ} {M : ℝ}

/-- The actual smooth-band density is integrable for every Hilbert datum
(`app:ch_waves:eq:B-bounds`). No regularity of the datum is assumed. -/
theorem integrable_wideDensity (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    Integrable (weightedWideDensity d v) :=
  (integrable_density (radius := refinedRadius (J := J))
    (fun i ↦ measurable_weightedRadialBand hd i.1.val)
    (fun i ↦ norm_weightedRadialBand_le hb i.1.val) (wideRefinement n J v)).congr
    (weightedWideDensity_eq_refined hd hM hb v).symm

/-- All polynomial moments of the literal density are integrable
(`app:ch_waves:thm:individual`). -/
theorem integrable_wideDensity_moment (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) (m : ℕ) :
    Integrable (fun η ↦ ‖η‖ ^ m * ‖weightedWideDensity d v η‖) := by
  apply (integrable_density_moment (radius := refinedRadius (J := J))
    (fun i ↦ measurable_weightedRadialBand hd i.1.val)
    (fun i ↦ norm_weightedRadialBand_le hb i.1.val) (wideRefinement n J v)
    (K := (2 : ℝ) ^ J) (by positivity) refinedRadius_le_ceiling m).congr
  filter_upwards [weightedWideDensity_eq_refined hd hM hb v] with η hη
  rw [hη]

/-- The original smooth density vanishes at and beyond its dyadic ceiling,
pointwise for its literal representative (`app:ch_waves:thm:individual`). -/
theorem wideDensity_eq_zero_of_ceiling_le (d : Euclidean (n - 1) → ℂ)
    (v : WideInput n J) {η : Euclidean (n - 1)} (hη : (2 : ℝ) ^ J ≤ ‖η‖) :
    weightedWideDensity d v η = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : 4 * dyadicScale j.val ≤ ‖η‖ := by
    have hp : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have he : 4 * dyadicScale j.val = (2 : ℝ) ^ (j.val + 1) := by
      simp only [dyadicScale, pow_succ]
      ring
    exact he ▸ hp.trans hη
  simp [weightedRadialBand, radialBand, scalarBand_eq_zero_of_ge hj]

/-- The literal rounding used by the mean recurrence has outer radius `4K`.
This is a Fourier-input statement before physical multiplication
(`app:ch_waves:thm:individual`). -/
theorem wideDensity_eq_zero_of_four_mul_le {K : ℝ} (hK : 1 ≤ K)
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n (cutoffCount K))
    {η : Euclidean (n - 1)} (hη : 4 * K ≤ ‖η‖) :
    weightedWideDensity d v η = 0 :=
  wideDensity_eq_zero_of_ceiling_le d v ((cutoffCount_ceiling hK).trans hη)

/-- The actual floor-one high-pass is preserved by every smooth band
(`app:ch_background:defn:bg-row`). -/
theorem wideDensity_eq_zero_of_highPass (d : Euclidean (n - 1) → ℂ)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → d η = 0) (v : WideInput n J)
    {η : Euclidean (n - 1)} (hη : ‖η‖ ≤ 1) :
    weightedWideDensity d v η = 0 := by
  simp [weightedWideDensity, weightedRadialBand, hfloor η hη]

/-- Density additivity uses equality almost everywhere of `L²` representatives,
not a pointwise choice of representatives (`app:ch_waves:eq:WKB-W`). -/
theorem wideDensity_add (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M)
    (v w : WideInput n J) :
    weightedWideDensity d (v + w) =ᵐ[volume]
      fun η ↦ weightedWideDensity d v η + weightedWideDensity d w η := by
  have hs := weightedWideSynthesis_coeFn hd hb (v + w)
  rw [map_add] at hs
  filter_upwards [hs, Lp.coeFn_add (weightedWideSynthesis hd hb v)
    (weightedWideSynthesis hd hb w), weightedWideSynthesis_coeFn hd hb v,
    weightedWideSynthesis_coeFn hd hb w] with η hη ha hv hw
  exact hη.symm.trans (ha.trans (congrArg₂ (· + ·) hv hw))

/-- Complex linearity retains both quadratures of the original annular datum
(`app:ch_waves:eq:WKB-W`). -/
theorem wideDensity_smul (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M)
    (c : ℂ) (v : WideInput n J) :
    weightedWideDensity d (c • v) =ᵐ[volume] fun η ↦ c * weightedWideDensity d v η := by
  have hs := weightedWideSynthesis_coeFn hd hb (c • v)
  rw [map_smul] at hs
  filter_upwards [hs, Lp.coeFn_smul c (weightedWideSynthesis hd hb v),
    weightedWideSynthesis_coeFn hd hb v] with η hη ha hv
  exact hη.symm.trans (ha.trans (congrArg (c * ·) hv))

/-- The inverse Fourier integrand is integrable, with unit-modulus radian
character (`app:ch_waves:eq:B-bounds`). -/
theorem integrable_wideField_integrand (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) (y : Euclidean (n - 1)) :
    Integrable (fun η ↦ Complex.exp ((inner ℝ η y : ℂ) * Complex.I) *
      weightedWideDensity d v η) := by
  have hf := integrable_wideDensity hd hM hb v
  apply hf.norm.mono'
    (((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul
        continuous_const)).aestronglyMeasurable).mul hf.aestronglyMeasurable)
  filter_upwards [] with η
  change ‖Complex.exp ((inner ℝ η y : ℂ) * Complex.I) *
    weightedWideDensity d v η‖ ≤ ‖weightedWideDensity d v η‖
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- The actual inverse Fourier field is additive (`app:ch_waves:eq:WKB-W`). -/
theorem wideField_add (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v w : WideInput n J) :
    weightedWideField d (v + w) = weightedWideField d v + weightedWideField d w := by
  funext y
  unfold weightedWideField
  simp only [Pi.add_apply]
  rw [← integral_add (integrable_wideField_integrand hd hM hb v y)
    (integrable_wideField_integrand hd hM hb w y)]
  apply integral_congr_ae
  filter_upwards [wideDensity_add hd hb v w] with η hη
  rw [hη, mul_add]

/-- Complex homogeneity of the actual initial field
(`app:ch_waves:eq:WKB-W`). -/
theorem wideField_smul (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M)
    (c : ℂ) (v : WideInput n J) :
    weightedWideField d (c • v) = c • weightedWideField d v := by
  funext y
  simp only [weightedWideField, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [wideDensity_smul hd hb c v] with η hη
  rw [hη]
  ring

/-- The spatial initial cutoff is applied after the original Lebesgue Fourier
synthesis (`app:ch_waves:thm:individual`). -/
def wideInitialData (χ : Euclidean (n - 1) → ℝ)
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) : Euclidean (n - 1) → ℂ :=
  fun y ↦ χ y • weightedWideField d v y

/-- The cut initial field is smooth for arbitrary Hilbert input
(`app:ch_waves:thm:individual`). -/
theorem contDiff_wideInitialData {χ : Euclidean (n - 1) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hd : Measurable d) (hM : 0 ≤ M)
    (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiff ℝ ∞ (wideInitialData χ d v) :=
  hχ.smul (contDiff_weightedWideField hd hM hb v)

/-- Spatial support concerns the initial position variable
(`app:ch_waves:thm:individual`). -/
theorem tsupport_wideInitialData_subset (χ : Euclidean (n - 1) → ℝ)
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    tsupport (wideInitialData χ d v) ⊆ tsupport χ :=
  tsupport_smul_subset_left _ _

/-- A compact initial cutoff yields compact support of the actual initial field
(`app:ch_waves:thm:individual`). -/
theorem hasCompactSupport_wideInitialData {χ : Euclidean (n - 1) → ℝ}
    (hχ : HasCompactSupport χ) (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    HasCompactSupport (wideInitialData χ d v) := hχ.smul_right

/-- Spatial localization does not change the field on the fixed plateau
(`app:ch_waves:thm:individual`). -/
theorem wideInitialData_eq_on_plateau {χ : Euclidean (n - 1) → ℝ}
    (d : Euclidean (n - 1) → ℂ) (v : WideInput n J)
    {y : Euclidean (n - 1)} (hy : χ y = 1) :
    wideInitialData χ d v y = weightedWideField d v y := by
  simp [wideInitialData, hy]

/-- The actual localized Lebesgue input operator preserves both complex
quadratures (`app:ch_waves:eq:WKB-W`). -/
def wideInitialDataLinearMap (χ : Euclidean (n - 1) → ℝ)
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) :
    WideInput n J →ₗ[ℂ] (Euclidean (n - 1) → ℂ) where
  toFun := wideInitialData χ d
  map_add' v w := by
    funext y
    change χ y • weightedWideField d (v + w) y =
      χ y • weightedWideField d v y + χ y • weightedWideField d w y
    rw [wideField_add hd hM hb, Pi.add_apply, smul_add]
  map_smul' c v := by
    funext y
    simp only [wideInitialData, wideField_smul hd hb, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

end JanetCartan.RawPrimary
