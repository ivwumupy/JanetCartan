module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.HilbertRefinement.Band

/-! # Reassembly of the half-derivative channel

The smooth wide-band mask is multiplied by `sqrt ‖η‖` on the original datum.
The sharp indicators disappear after reassembly, before any smooth symbol
calculus in `app:ch_waves:thm:individual`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

variable {n j : ℕ} {M : ℝ} {β : Euclidean (n - 1) → ℂ}

/-- Measurability on each smaller sharp annulus follows from the wide band
(`app:ch_waves:thm:individual`). -/
theorem refinedMask_measurable (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j)))
    (b : Fin 2) : AEStronglyMeasurable β (annularMeasure n ((2 : ℝ) ^ (j + b.val))) :=
  hβ.mono_measure (Measure.restrict_mono (annulus_subset_wideBand n j b) le_rfl)

/-- The same mask bound holds on both sharp components
(`app:ch_waves:eq:B-bounds`). -/
theorem refinedMask_bound (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M)
    (b : Fin 2) : ∀ᵐ η ∂annularMeasure n ((2 : ℝ) ^ (j + b.val)), ‖β η‖ ≤ M :=
  ae_mono (Measure.restrict_mono (annulus_subset_wideBand n j b) le_rfl) hb

/-- Measurability of the literal coefficient on the original wide band
(`app:ch_waves:eq:B-bounds`). -/
theorem wideHalfCoefficient_measurable
    (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j))) :
    AEStronglyMeasurable (halfCoefficient β) (volume.restrict (wideBand n j)) :=
  (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).aestronglyMeasurable.mul hβ

/-- The half-derivative bound on the original wide band
(`app:ch_waves:eq:B-bounds`). -/
theorem wideHalfCoefficient_bound
    (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M) :
    ∀ᵐ η ∂volume.restrict (wideBand n j),
      ‖halfCoefficient β η‖ ≤ Real.sqrt (4 * dyadicScale j) * M := by
  filter_upwards [hb, ae_restrict_mem (measurableSet_wideBand n j)] with η hβ hη
  have hηR : ‖η‖ ≤ 4 * dyadicScale j := by simpa using hη.1
  simp only [halfCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (Real.sqrt_le_sqrt hηR) hβ (norm_nonneg _) (Real.sqrt_nonneg _)

/-- The actual wide-band channel, multiplying the original datum by the original
mask and `sqrt ‖η‖` (`app:ch_waves:thm:individual`). -/
def wideChannel (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j)))
    (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M) :
    WideBandL2 n j →L[ℂ] Output n :=
  (zeroExtension (measurableSet_wideBand n j)).toContinuousLinearMap.comp
    (boundedMultiplier (wideHalfCoefficient_measurable hβ) (wideHalfCoefficient_bound hb))

/-- Literal density of the constructed wide channel
(`app:ch_waves:thm:individual`). -/
theorem wideChannel_coeFn (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j)))
    (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M) (f : WideBandL2 n j) :
    wideChannel hβ hb f =ᵐ[volume]
      (wideBand n j).indicator (fun η ↦ halfCoefficient β η * f η) := by
  exact (zeroExtension_coeFn (measurableSet_wideBand n j) _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (measurableSet_wideBand n j)).mp
      (boundedMultiplier_coeFn (wideHalfCoefficient_measurable hβ) (wideHalfCoefficient_bound hb) f))

/-- For a supported mask the reassembled coefficient has no remaining sharp
indicator (`app:ch_waves:thm:individual`). -/
theorem wideChannel_coeFn_of_support
    (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j)))
    (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M)
    (hs : ∀ η, η ∉ wideBand n j → β η = 0) (f : WideBandL2 n j) :
    wideChannel hβ hb f =ᵐ[volume] fun η ↦ halfCoefficient β η * f η := by
  filter_upwards [wideChannel_coeFn hβ hb f] with η hη
  rw [hη]
  by_cases hm : η ∈ wideBand n j
  · exact Set.indicator_of_mem hm _
  · rw [Set.indicator_of_notMem hm, halfCoefficient, hs η hm, mul_zero, zero_mul]

/-- The constructed radial mask supplies the actual wide-band measurability
hypothesis (`app:ch_waves:thm:individual`). -/
theorem radialBand_complex_measurable (n j : ℕ) :
    AEStronglyMeasurable (fun η ↦ (radialBand n j η : ℂ)) (volume.restrict (wideBand n j)) :=
  (Complex.measurable_ofReal.comp (measurable_radialBand n j)).aestronglyMeasurable

/-- The constructed radial mask supplies the actual bound, with constant one
(`app:ch_waves:eq:B-bounds`). -/
theorem radialBand_complex_bound (n j : ℕ) :
    ∀ᵐ η ∂volume.restrict (wideBand n j), ‖(radialBand n j η : ℂ)‖ ≤ 1 := by
  apply Filter.Eventually.of_forall
  intro η
  have h := bandProfile_mem (‖η‖ / dyadicScale j)
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    radialBand, scalarBand, abs_of_nonneg h.1] using h.2

/-- The actual radial channel has the original smooth coefficient after
reassembly; its support hypothesis is proved, not assumed
(`app:ch_waves:thm:individual`). -/
theorem radialWideChannel_coeFn (n j : ℕ) (f : WideBandL2 n j) :
    wideChannel (radialBand_complex_measurable n j) (radialBand_complex_bound n j) f =ᵐ[volume]
      fun η ↦ (Real.sqrt ‖η‖ : ℂ) * (radialBand n j η : ℂ) * f η := by
  apply wideChannel_coeFn_of_support
  intro η hη
  simp only [radialBand_eq_zero_off_wideBand hη, Complex.ofReal_zero]

/-- Refining a wide datum leaves its actual half-derivative output unchanged
(`app:ch_waves:thm:individual`). -/
theorem wideChannel_eq_refined (hβ : AEStronglyMeasurable β (volume.restrict (wideBand n j)))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂volume.restrict (wideBand n j), ‖β η‖ ≤ M)
    (f : WideBandL2 n j) :
    wideChannel hβ hb f = ∑ b : Fin 2,
      channel (refinedMask_measurable hβ b) hM (refinedMask_bound hb b)
        (bandRestriction n j f b) := by
  rw [Fin.sum_univ_two]
  apply Lp.ext
  have hr (b : Fin 2) := (ae_restrict_iff'
    (measurableSet_annulus n ((2 : ℝ) ^ (j + b.val)))).mp
      (bandRestriction_coeFn n j f b)
  filter_upwards [wideChannel_coeFn hβ hb f,
    Lp.coeFn_add
      (channel (refinedMask_measurable hβ 0) hM (refinedMask_bound hb 0) (bandRestriction n j f 0))
      (channel (refinedMask_measurable hβ 1) hM (refinedMask_bound hb 1) (bandRestriction n j f 1)),
    channel_coeFn (refinedMask_measurable hβ 0) hM (refinedMask_bound hb 0) (bandRestriction n j f 0),
    channel_coeFn (refinedMask_measurable hβ 1) hM (refinedMask_bound hb 1) (bandRestriction n j f 1),
    hr 0, hr 1, ae_not_mem_both_annuli n j] with η hw hs h₀ h₁ hr₀ hr₁ hd
  rw [hw, hs, Pi.add_apply, h₀, h₁]
  unfold channelDensity
  by_cases hw : η ∈ wideBand n j
  · rw [Set.indicator_of_mem hw]
    rw [wideBand_eq_union] at hw
    rcases hw with h | h
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (fun h' ↦ hd ⟨h, h'⟩),
        add_zero, hr₀ h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' ↦ hd ⟨h', h⟩), Set.indicator_of_mem h,
        zero_add, hr₁ h]
      rfl
  · rw [Set.indicator_of_notMem hw,
      Set.indicator_of_notMem (fun h ↦ hw (annulus_subset_wideBand n j 0 h)),
      Set.indicator_of_notMem (fun h ↦ hw (annulus_subset_wideBand n j 1 h)), add_zero]

end JanetCartan.RawInputPartition
