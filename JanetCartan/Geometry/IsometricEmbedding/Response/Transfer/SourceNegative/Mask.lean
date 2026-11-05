module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.ShellLoss
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth radial shell mask

The mask needed by the original-source estimate in
`app:ch_response:prop:response-graded` is constructed here, rather than assumed
as an additional analytic input. Its complementary bound is exactly one.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.SourceNegative

/-- A smooth radial mask for the source-shell theorem, with complementary
bound one (`app:ch_osc:prop:osc-source-shell`). -/
theorem exists_sourceShellMask {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {c G ρ : ℝ}
    (hc : 0 < c) (hG : 0 < G) (hρ : 0 < ρ) :
    ∃ π : (E →L[ℝ] ℝ) → ℂ, Localization.SourceShellMask π c G ρ 1 := by
  let lo : ContDiffBump (0 : E →L[ℝ] ℝ) :=
    ⟨c * ρ / 4, c * ρ / 2, by positivity, by nlinarith [mul_pos hc hρ]⟩
  let hi : ContDiffBump (0 : E →L[ℝ] ℝ) :=
    ⟨2 * G * ρ, 4 * G * ρ, by positivity, by nlinarith [mul_pos hG hρ]⟩
  let b : (E →L[ℝ] ℝ) → ℝ := fun ξ ↦ (1 - lo ξ) * hi ξ
  have hb (ξ) : 0 ≤ b ξ ∧ b ξ ≤ 1 := by
    dsimp [b]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr lo.le_one) hi.nonneg
    · exact (mul_le_mul_of_nonneg_left hi.le_one (sub_nonneg.mpr lo.le_one)).trans
        (by linarith [lo.nonneg (x := ξ)])
  refine ⟨fun ξ ↦ (b ξ : ℂ), ?_⟩
  refine {
    smooth := Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub lo.contDiff).mul hi.contDiff)
    equals_one := ?_
    support := ?_
    bound_nonneg := zero_le_one
    complement_bound := ?_ }
  · intro ξ hl hu
    have hlo : lo ξ = 0 := lo.zero_of_le_dist (by simpa [lo, dist_zero_right] using hl)
    have hhi : hi ξ = 1 := hi.one_of_mem_closedBall (by simpa [hi, dist_zero_right] using hu)
    simp [b, hlo, hhi]
  · apply closure_minimal
    · intro ξ hξ
      have hl : c * ρ / 4 ≤ ‖ξ‖ := by
        by_contra hn
        have hlo : lo ξ = 1 := lo.one_of_mem_closedBall (by
          simpa [lo, dist_zero_right] using (le_of_lt (lt_of_not_ge hn)))
        exact hξ (by simp [b, hlo])
      have hu : ‖ξ‖ ≤ 4 * G * ρ := by
        by_contra hn
        have hhi : hi ξ = 0 := hi.zero_of_le_dist (by
          simpa [hi, dist_zero_right] using (le_of_lt (lt_of_not_ge hn)))
        exact hξ (by simp [b, hhi])
      exact ⟨hl, hu⟩
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  · intro ξ
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hb ξ).2)]
    linarith [(hb ξ).1]

end JanetCartan.ResponseTransfer.SourceNegative
