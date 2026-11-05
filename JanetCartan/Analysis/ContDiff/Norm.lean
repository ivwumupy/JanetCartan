module

public import JanetCartan.Analysis.ContDiff.Norm.Interpolation

/-!
# Completed norm statements

The original manuscript statements, assembled from their constructive leaf proofs.
Shared definitions live in `Norm/Defs.lean` to keep the import graph acyclic.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix B, app:lem:elementary-interpolation-jets: interpolation on a closed ball. -/
theorem cNorm_le_interpolation [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) j f ≤
        C * (cNorm (Metric.closedBall x ρ) R f) ^ (1 - (j - R : ℝ) / (k - R)) *
          (cNorm (Metric.closedBall x ρ) k f) ^ ((j - R : ℝ) / (k - R)) := by
  exact cNorm_le_interpolation_closedBall x hρ hRj hjk

end JanetCartan
