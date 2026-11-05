module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplierBounds.Integrands

/-!
# The exact far complement of the physical source remainder

The endpoint difference, rather than a near-chart Taylor approximation, is
used on the complement in `app:ch_regular_base:eq:fixed-source-multiplication`.
The only amplitude bound here is on its actual global extension. Consequently
angular shoulders, bounded frequencies, and all phase oscillations are kept.
This proves arbitrary decay of the zeroth seminorm. Differentiated endpoint
expressions require the corresponding polynomial growth estimates separately.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace JanetCartan.FourierIntegral.SourceBounds

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Any part of the far complement is bounded by higher moments of the same
source, without altering the operator (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem norm_far_sourceRemainder_le
    (m : 𝓢(Euclidean n, ℂ)) (S : Euclidean n → ℝ) (A : Euclidean n → F)
    {C R : ℝ} (hA : ∀ ξ, ‖A ξ‖ ≤ C) (hR : 0 < R)
    (η : Euclidean n) (N : ℕ) (s : Set (Euclidean n))
    (hfar : s ⊆ {v | R ≤ ‖v‖}) :
    ‖∫ v in s, physicalSourceDensity m v • endpointDifference S A η v‖ ≤
      2 * C * ((R ^ N)⁻¹ * sourceMoment (physicalSourceDensity m) N) := by
  have hC : 0 ≤ C := (norm_nonneg (A 0)).trans (hA 0)
  calc
    _ ≤ ∫ v in s, (2 * C) * ‖physicalSourceDensity m v‖ := by
      apply norm_integral_le_of_norm_le
        ((physicalSourceDensity m).integrable.norm.const_mul _).integrableOn
      filter_upwards [] with v
      rw [norm_smul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (norm_endpointDifference_le S A hA η v)
          (norm_nonneg (physicalSourceDensity m v))
    _ = 2 * C * ∫ v in s, ‖physicalSourceDensity m v‖ := integral_const_mul _ _
    _ ≤ 2 * C * ∫ v in {v : Euclidean n | R ≤ ‖v‖},
        ‖physicalSourceDensity m v‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set (physicalSourceDensity m).integrable.norm.integrableOn
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Filter.Eventually.of_forall hfar)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using sourceMoment_tail_le (physicalSourceDensity m) 0 N hR

end JanetCartan.FourierIntegral.SourceBounds
