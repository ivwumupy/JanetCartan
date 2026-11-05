module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Geometry
public import JanetCartan.Analysis.Microlocal.Localization.Gap

/-!
# From the protected signed directions to the full Fourier gap

The compact angular buffer in `app:ch_pairs:setup:pairs-lag` gives a distance
between every normalized signed gradient and the nonzero complementary mask.
Together with the original lower gradient bound, this implies the full
`c * (rho + |eta|)` gap used in `FullMask`, at every radius including zero.
The mask is not truncated and no higher-frequency assumption is introduced.
-/

@[expose] public noncomputable section

namespace JanetCartan.SignedProductEstimates

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalizing two nonzero directions costs at most twice their original
separation (`app:ch_pairs:setup:pairs-lag`). This gives the full angular gap
without a radius-dependent constant. -/
private theorem norm_mul_normalized_difference_le {u v : E} (hv : v ≠ 0) :
    ‖u‖ * ‖normalize u - normalize v‖ ≤ 2 * ‖u - v‖ := by
  have he : ‖u‖ • (normalize u - normalize v) =
      (u - v) + (‖v‖ - ‖u‖) • normalize v := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  calc
    _ = ‖‖u‖ • (normalize u - normalize v)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
    _ ≤ ‖u - v‖ + ‖(‖v‖ - ‖u‖) • normalize v‖ := by rw [he]; exact norm_add_le _ _
    _ = ‖u - v‖ + |‖v‖ - ‖u‖| := by rw [norm_smul, norm_normalize hv, mul_one, Real.norm_eq_abs]
    _ ≤ ‖u - v‖ + ‖u - v‖ := by
      apply add_le_add le_rfl
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
    _ = _ := by ring

/-- The original angular distance and lower gradient band imply a full
Fourier gap, including zero and arbitrarily large covectors
(`app:ch_pairs:setup:pairs-lag`). The constant is explicit and independent of
the true frequency, source point and chosen samples. This supplies the
`hgap` input of `exists_signed_full_mask_tail_constant`. -/
theorem full_frequency_gap_of_normalized_distance
    {g η : E} {a δ ρ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hgl : a ≤ ‖g‖)
    (hangle : η ≠ 0 → δ ≤ dist (normalize g) (normalize η)) :
    (min δ 1 * min a 1 / 4) * (ρ + ‖η‖) ≤ ‖ρ • g - η‖ := by
  have hapos : 0 < min a 1 := lt_min ha zero_lt_one
  have hdpos : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hamin : min a 1 ≤ a := min_le_left _ _
  have haone : min a 1 ≤ 1 := min_le_right _ _
  have hdmin : min δ 1 ≤ δ := min_le_left _ _
  have hdone : min δ 1 ≤ 1 := min_le_right _ _
  have hnorm : ‖ρ • g‖ = ρ * ‖g‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  by_cases hη : η = 0
  · simp only [hη, norm_zero, add_zero, sub_zero, hnorm]
    have hconst : min δ 1 * min a 1 / 4 ≤ a := by nlinarith
    exact (mul_le_mul_of_nonneg_right hconst hρ.le).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hgl hρ.le])
  · have hgnz : g ≠ 0 := norm_pos_iff.mp (ha.trans_le hgl)
    have hunz : ρ • g ≠ 0 := smul_ne_zero hρ.ne' hgnz
    have hdist : min δ 1 ≤ ‖normalize (ρ • g) - normalize η‖ := by
      rw [normalize_smul_of_pos hρ]
      exact hdmin.trans (by simpa only [dist_eq_norm] using hangle hη)
    have hu := norm_mul_normalized_difference_le (u := ρ • g) hη
    have hv := norm_mul_normalized_difference_le (u := η) hunz
    rw [norm_sub_rev (normalize η), norm_sub_rev η] at hv
    have hleft := mul_le_mul_of_nonneg_left hdist (norm_nonneg (ρ • g))
    have hright := mul_le_mul_of_nonneg_left hdist (norm_nonneg η)
    have hscale : min a 1 * (ρ + ‖η‖) ≤ ‖ρ • g‖ + ‖η‖ := by
      rw [hnorm]
      nlinarith [mul_le_mul_of_nonneg_right (hamin.trans hgl) hρ.le,
        mul_le_mul_of_nonneg_right haone (norm_nonneg η)]
    have hscaled := mul_le_mul_of_nonneg_left hscale hdpos.le
    nlinarith

/-- Positivity of the single full-gap constant in
`app:ch_pairs:setup:pairs-lag`. It is fixed before all signed samples and
frequencies, as required by the full-mask source estimate. -/
theorem full_frequency_gap_constant_pos {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < min δ 1 * min a 1 / 4 := by positivity

/-- Radial low/high pieces and the protected angular buffer give ONE gap
on the full complementary mask (`app:ch_pairs:setup:pairs-lag`). Angular
separation is needed only on the middle radial band, so bounded-frequency
pieces and radial shoulders are retained. `K` is the original common signed
direction set, populated by `sampled_plus_mem_angularSet` and
`sampled_minus_mem_angularSet`; it is never reselected for a sample. -/
theorem full_frequency_gap_of_buffered_mask
    {K : Set E} {g η : E} {a G δ ρ : ℝ}
    (ha : 0 < a) (hG : 0 < G) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hgl : a ≤ ‖g‖) (hgu : ‖g‖ ≤ G) (hgK : normalize g ∈ K)
    (hbuffer : a * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * G * ρ →
      ∀ v ∈ K, δ ≤ dist v (normalize η)) :
    min (JanetCartan.Localization.radialGapConstant a G) (min δ 1 * min a 1 / 4) *
      (ρ + ‖η‖) ≤ ‖ρ • g - η‖ := by
  have hsum : 0 ≤ ρ + ‖η‖ := by positivity
  by_cases hlo : ‖η‖ ≤ a * ρ / 2
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hsum).trans
      (JanetCartan.Localization.radial_frequency_gap ha hG hρ.le hgl hgu (Or.inl hlo))
  by_cases hhi : 2 * G * ρ ≤ ‖η‖
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hsum).trans
      (JanetCartan.Localization.radial_frequency_gap ha hG hρ.le hgl hgu (Or.inr hhi))
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hsum).trans
    (full_frequency_gap_of_normalized_distance ha hδ hρ hgl
      (fun _ ↦ hbuffer (le_of_not_ge hlo) (le_of_not_ge hhi) _ hgK))

/-- The full radial/angular gap remains positive with the original fixed
gradient and angular margins (`app:ch_pairs:setup:pairs-lag`). -/
theorem buffered_mask_gap_constant_pos {a G δ : ℝ}
    (ha : 0 < a) (hG : 0 < G) (hδ : 0 < δ) :
    0 < min (JanetCartan.Localization.radialGapConstant a G) (min δ 1 * min a 1 / 4) :=
  lt_min (JanetCartan.Localization.radialGapConstant_pos ha hG)
    (full_frequency_gap_constant_pos ha hδ)

end JanetCartan.SignedProductEstimates
