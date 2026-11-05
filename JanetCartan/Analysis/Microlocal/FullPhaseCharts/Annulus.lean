module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen

/-!
# Annular range of the normalized data map

Elementary estimates used for `app:ch_seed:eq:seed-normal-annulus`. The product
`ℝ × E` has its standard maximum norm; the transverse component uses the given
inner-product norm. The phase comparison needed to invoke these estimates is
not asserted here.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.FullPhaseCharts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Half-relative control of the transverse error gives the lower annular
bound in `app:ch_seed:eq:seed-normal-annulus`. -/
theorem norm_lower_of_transverse_close (q : ℝ × E) (η : E)
    (h : ‖q.2 - η‖ ≤ ‖η‖ / 2) : ‖η‖ / 2 ≤ ‖q‖ := by
  have ht : ‖η‖ ≤ ‖q.2‖ + ‖q.2 - η‖ := by
    simpa [norm_sub_rev] using norm_le_insert' η q.2
  linarith [norm_snd_le q]

/-- The frozen chart has a uniform upper bound from the reference velocity
and transverse covector bounds (`app:ch_seed:eq:seed-normal-annulus`). -/
theorem norm_frozenChart_le {v : ℝ → E} {u : ℝ × E} {M R : ℝ}
    (hM : ‖v u.1‖ ≤ M) (hR : ‖u.2‖ ≤ R) :
    ‖frozenChart v u‖ ≤ max M 1 * R := by
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_inner_le_norm _ _).trans (mul_le_mul
      (hM.trans (le_max_left _ _)) hR (norm_nonneg _) (le_trans zero_le_one (le_max_right _ _)))
  · calc
      ‖u.2‖ ≤ R := hR
      _ ≤ max M 1 * R := by
        have hR₀ : 0 ≤ R := (norm_nonneg u.2).trans hR
        nlinarith [le_max_right M 1]

/-- Uniform proximity to the frozen map preserves both sides of a fixed
annulus and the relative transverse bound. This is the elementary consequence
of phase comparison used in `app:ch_seed:eq:seed-normal-annulus`. -/
theorem annular_bounds_of_frozen_close {v : ℝ → E} {u q : ℝ × E}
    {m M R : ℝ} (hm : 0 < m) (hη : m ≤ ‖u.2‖)
    (hM : ‖v u.1‖ ≤ M) (hR : ‖u.2‖ ≤ R)
    (hclose : ‖q - frozenChart v u‖ ≤ m / 2) :
    ‖q.2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
      m / 2 ≤ ‖q‖ ∧ ‖q‖ ≤ max M 1 * R + m / 2 ∧ q ≠ 0 := by
  have ht : ‖q.2 - u.2‖ ≤ ‖u.2‖ / 2 :=
    (norm_snd_le (q - frozenChart v u)).trans (hclose.trans (by linarith))
  have hl : m / 2 ≤ ‖q‖ := (by linarith : m / 2 ≤ ‖u.2‖ / 2).trans
    (norm_lower_of_transverse_close q u.2 ht)
  refine ⟨ht, hl, ?_, ?_⟩
  · have h := norm_add_le (q - frozenChart v u) (frozenChart v u)
    rw [sub_add_cancel] at h
    linarith [norm_frozenChart_le hM hR]
  · intro hq
    rw [hq, norm_zero] at hl
    linarith

end JanetCartan.FullPhaseCharts
