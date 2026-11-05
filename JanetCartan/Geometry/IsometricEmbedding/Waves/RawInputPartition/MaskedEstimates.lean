module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.MaskedSynthesis

/-!
# Bounds for the original masked wide-band data

The finite-refinement bounds are instantiated with the constructed radial
masks and transferred through the norm-preserving identification. The density
and inverse Fourier field here use the original smooth bands, with no sharp
indicator remaining. The constants in `app:ch_waves:eq:B-bounds` depend only
on dimension, derivative order and the bound of the given detector/high-pass.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert
variable {n J : ℕ}

/-- Original smooth-band density, before any spatial initial cutoff
(`app:ch_waves:thm:individual`). -/
def weightedWideDensity (d : Euclidean (n - 1) → ℂ) (v : WideInput n J)
    (η : Euclidean (n - 1)) : ℂ :=
  ∑ j : Fin J, (Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η * v j η

/-- The original synthesis has the original smooth density representative
(`app:ch_waves:thm:individual`). -/
theorem weightedWideSynthesis_coeFn {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    weightedWideSynthesis hd hb v =ᵐ[volume] weightedWideDensity d v := by
  rw [weightedWideSynthesis, wideSynthesis_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have ha := Filter.eventually_all.mpr (fun j : Fin J ↦ wideChannel_coeFn_of_support
    (measurable_weightedRadialBand hd j.val).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_weightedRadialBand_le hb j.val))
    (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand d hη) (v j))
  filter_upwards [ha] with η hη
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ ↦ hη j)

/-- Actual equality of the smooth wide density with the refined density
(`app:ch_waves:eq:B-bounds`). -/
theorem weightedWideDensity_eq_refined {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    weightedWideDensity d v =ᵐ[volume]
      density (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val) (wideRefinement n J v) := by
  refine (weightedWideSynthesis_coeFn hd hb v).symm.trans ?_
  rw [weightedWideSynthesis_eq_refined hd hM hb]
  change weightedRefinedSynthesis hd hM hb (wideRefinement n J v) =ᵐ[volume] _
  exact synthesis_coeFn
    (fun i : RefinedIndex J ↦ (measurable_weightedRadialBand hd i.1.val).aestronglyMeasurable)
    (fun _ ↦ hM) (fun i ↦ Filter.Eventually.of_forall (norm_weightedRadialBand_le hb i.1.val)) _

/-- The actual initial field, in the original radian inverse-Fourier convention
(`app:ch_waves:thm:individual`). -/
def weightedWideField (d : Euclidean (n - 1) → ℂ) (v : WideInput n J)
    (x : Euclidean (n - 1)) : ℂ :=
  ∫ η, Complex.exp ((inner ℝ η x : ℂ) * Complex.I) * weightedWideDensity d v η

/-- The original and refined inverse-Fourier fields agree everywhere
(`app:ch_waves:thm:individual`). -/
theorem weightedWideField_eq_refined {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    weightedWideField d v =
      field (fun i : RefinedIndex J ↦ weightedRadialBand d i.1.val) (wideRefinement n J v) := by
  funext x
  rw [field_eq_integral_exp]
  exact integral_congr_ae ((weightedWideDensity_eq_refined hd hM hb v).mono
    (fun η hη ↦ congrArg (fun t ↦ Complex.exp ((inner ℝ η x : ℂ) * Complex.I) * t) hη))

/-- Smoothness of the actual wide-band field follows from the literal Fourier
construction, with no new smoothness premise (`app:ch_waves:thm:individual`). -/
theorem contDiff_weightedWideField {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiff ℝ ∞ (weightedWideField d v) := by
  rw [weightedWideField_eq_refined hd hM hb]
  exact contDiff_field (radius := refinedRadius (J := J))
    (fun i ↦ measurable_weightedRadialBand hd i.1.val)
    (fun i ↦ norm_weightedRadialBand_le hb i.1.val) (wideRefinement n J v)
    (K := (2 : ℝ) ^ J) (by positivity) refinedRadius_le_ceiling

/-- Fourier `L¹` for the original wide data, with exactly their original norm
and a fixed refinement factor (`app:ch_waves:eq:B-bounds`). -/
theorem integral_norm_weightedWideDensity_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) :
    (∫ η, ‖weightedWideDensity d v η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ := by
  rw [integral_congr_ae ((weightedWideDensity_eq_refined hd hM hb v).mono (fun _ he ↦ congrArg norm he))]
  simpa only [norm_wideRefinement] using integral_norm_density_refined_rounded_le hn hK
    (fun i ↦ measurable_weightedRadialBand hd i.1.val) hM
    (fun i ↦ norm_weightedRadialBand_le hb i.1.val) (wideRefinement n (cutoffCount K) v)

/-- Initial `C^m` for the actual wide-band field, with a constant independent
of scale count (`app:ch_waves:eq:B-bounds`). -/
theorem cNorm_weightedWideField_rounded_le (hn : 1 ≤ n) {K : ℝ} (hK : 1 ≤ K)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) (m : ℕ) (s : Set (Euclidean (n - 1))) :
    cNorm s m (weightedWideField d v) ≤
      (((m + 1 : ℕ) : ℝ) * refinedFourierConstant n M * 4 ^ ((m : ℝ) + (n : ℝ) / 2)) *
        K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ := by
  rw [weightedWideField_eq_refined hd hM hb]
  simpa only [norm_wideRefinement] using cNorm_field_refined_rounded_le hn hK
    (fun i ↦ measurable_weightedRadialBand hd i.1.val) hM
    (fun i ↦ norm_weightedRadialBand_le hb i.1.val) (wideRefinement n (cutoffCount K) v) m s

/-- Hilbert synthesis bound for the original wide data. The two-shell
refinement loses only the fixed constant `√3 √4`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_weightedWideSynthesis_rounded_le {K : ℝ} (hK : 1 ≤ K)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) :
    ‖weightedWideSynthesis (J := cutoffCount K) hd hb‖ ≤
      (M * Real.sqrt 3 * Real.sqrt 4) * Real.sqrt K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [weightedWideSynthesis_eq_refined hd hM hb, ContinuousLinearMap.comp_apply]
  change ‖weightedRefinedSynthesis hd hM hb (wideRefinement n (cutoffCount K) v)‖ ≤ _
  apply ((weightedRefinedSynthesis hd hM hb).le_opNorm _).trans
  rw [norm_wideRefinement]
  exact mul_le_mul_of_nonneg_right
    (norm_synthesis_refined_rounded_le hK _ hM _) (norm_nonneg v)

end JanetCartan.RawInputPartition
