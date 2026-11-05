module

public import JanetCartan.Analysis.Sobolev.Local.Embedding.WeakLimit
public import JanetCartan.Analysis.Sobolev.Local.Embedding.ZeroDimension
public import JanetCartan.Analysis.Sobolev.Local.Embedding.SmoothOneDimension
public import JanetCartan.Analysis.Sobolev.Local.Embedding.SmoothHigherDimension

/-!
# Local Sobolev embedding

The quantitative H¹-to-Lᵖ embedding on a ball used in
`app:ch_regular:thm:exact-correction`, with the weak restriction norm of
`app:not:fourier`. The estimate holds for arbitrary weak data: mollification
passes the smooth estimates to each whole-space extension, and taking the
infimum over those extensions gives the restriction norm bound.

All dimensions are covered, including zero, one, and two. The exponent and
constant depend on the ball and target space, but are uniform over the input.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The local H¹-to-Lᵖ estimate used at the start of the proof of
`app:ch_regular:thm:exact-correction`. The exponent is finite and strictly
greater than two, and the estimate uses the infimum over actual weak
whole-space extensions (`app:not:fourier`), with no smoothness assumption on
the local L² class. -/
theorem exists_memLp_and_norm_le_restrictionSobolevNorm_ball
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ∃ p : ℝ≥0, 2 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ u : LocalL2 (ball c R) F, MemRestrictionSobolev (ball c R) 1 u →
        MemLp (u : EuclideanSpace ℝ (Fin n) → F) (p : ℝ≥0∞)
          (volume.restrict (ball c R)) ∧
        (eLpNorm u (p : ℝ≥0∞) (volume.restrict (ball c R))).toReal ≤
          C * restrictionSobolevNorm (ball c R) 1 u := by
  rcases n with _ | n
  · refine ⟨4, by norm_num, 1, by norm_num, fun u hu ↦ ?_⟩
    simpa using memLp_four_and_norm_le_restrictionSobolevNorm_zero_dimension c hR hu
  · obtain ⟨p, C, hp, hC, hsmooth⟩ :
        ∃ p C : ℝ≥0, 2 < p ∧ 0 < C ∧
          ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → F,
            ContDiff ℝ ∞ g → MemLp g 2 volume →
            MemLp (iteratedFDeriv ℝ 1 g) 2 volume →
            eLpNorm g p (volume.restrict (ball c R)) ≤ C *
              (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
      rcases n with _ | n
      · exact exists_smooth_eLpNorm_le_one_dimension c hR
      · exact exists_smooth_eLpNorm_le_ball_of_two_le_dimension (by omega) c hR
    exact ⟨p, hp, C, hC, fun _ hu ↦
      memLp_and_norm_le_restrictionSobolevNorm_of_smooth_estimate hC hsmooth hu⟩

end JanetCartan.LocalSobolev
