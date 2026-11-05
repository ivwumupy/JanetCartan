module

public import JanetCartan.Analysis.ContDiff.Norm.Interpolation.ScaleBounds.DerivativeBounds
public import JanetCartan.Analysis.ContDiff.Norm.Interpolation.ScaleBounds.Sequence

/-!
# Scale bounds on a closed ball

The two-term estimate used in `app:lem:elementary-interpolation-jets` in paper.tex.
Inward segments give an adjacent-order estimate on the ball, and scalar sequence
interpolation gives the arbitrary-order estimate. The constants are uniform in
the smooth function and the scale, with scale cutoff equal to one.
-/

public section

open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the two-term C-norm
scale estimate on a closed ball. The constants are independent of the smooth
function and the scale. The proof uses inward segments and finite-sequence
interpolation, so the codomain need not be complete and the domain need not
carry an inner product. -/
theorem exists_cNorm_scale_estimate [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ A : ℝ, 0 < A ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ f : E → F, ContDiff ℝ ∞ f → ∀ t : ℝ, 0 < t → t ≤ t₀ →
        cNorm (Metric.closedBall x ρ) j f ≤
          A * (t ^ (R - j : ℝ) * cNorm (Metric.closedBall x ρ) R f +
            t ^ (k - j : ℝ) * cNorm (Metric.closedBall x ρ) k f) := by
  obtain ⟨A, hA, hscale⟩ := CNormInterpolation.exists_sequence_scale_estimate
    (C := 1 + 2 / ρ + 5 * ρ) (by positivity) hRj hjk
  refine ⟨A, hA, 1, zero_lt_one, ?_⟩
  intro f hf t ht ht1
  apply hscale (fun n ↦ cNorm (Metric.closedBall x ρ) n f) ?_ ?_ t ht ht1
  · intro n
    exact Finset.sum_nonneg
      (fun i _ ↦ CNormInterpolation.derivativeSup_nonneg (Metric.closedBall x ρ) i f)
  · intro n s hs hs1
    exact CNormInterpolation.cNorm_succ_le_scale x hρ hf n hs hs1

end JanetCartan
