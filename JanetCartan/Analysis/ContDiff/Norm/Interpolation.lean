module

public import JanetCartan.Analysis.ContDiff.Norm.Interpolation.Optimization
public import JanetCartan.Analysis.ContDiff.Norm.Interpolation.ScaleBounds

/-!
# Interpolation of derivative norms on closed balls

The interpolation estimate of `app:lem:elementary-interpolation-jets` in paper.tex,
using the actual derivative seminorms. The general optimization lemma takes a
two-term scale estimate as a premise. On closed balls, the inward-segment and
finite-sequence estimates in `ScaleBounds` discharge that premise, giving
`cNorm_le_interpolation_closedBall` with the exact exponent `(j - R) / (k - R)`.
The public `cNorm_le_interpolation` theorem in `Norm.lean` now applies this proof.
-/

public section

open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace CNormInterpolation

/-- Appendix B, `app:lem:elementary-interpolation-jets`: derivative seminorms
are nonnegative. Analytic uses still require bounded derivative images. -/
theorem cNorm_nonneg (s : Set E) (r : ℕ) (f : E → F) : 0 ≤ cNorm s r f := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the direct bound
between derivative seminorms at ordered nonnegative integer orders. -/
theorem cNorm_mono (s : Set E) (f : E → F) {r k : ℕ} (hrk : r ≤ k) :
    cNorm s r f ≤ cNorm s k f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrk 1))
  intro i _ _
  apply Real.sSup_nonneg
  rintro _ ⟨x, _, rfl⟩
  exact norm_nonneg _

end CNormInterpolation

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the exact exponent
`(j - R) / (k - R)` follows from the two-term estimate at small scales.
This is conditional on that analytic estimate, uniformly over smooth functions. -/
theorem cNorm_le_interpolation_of_scale_estimate (s : Set E)
    {R j k : ℕ} (hRj : R < j) (hjk : j < k)
    (hscale : ∃ A : ℝ, 0 < A ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ f : E → F, ContDiff ℝ ∞ f → ∀ t : ℝ, 0 < t → t ≤ t₀ →
        cNorm s j f ≤ A * (t ^ (R - j : ℝ) * cNorm s R f +
          t ^ (k - j : ℝ) * cNorm s k f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm s j f ≤
        C * (cNorm s R f) ^ (1 - (j - R : ℝ) / (k - R)) *
          (cNorm s k f) ^ ((j - R : ℝ) / (k - R)) := by
  obtain ⟨A, hA, t₀, ht₀, hscale⟩ := hscale
  refine ⟨A * t₀ ^ (R - j : ℝ) + A * t₀ ^ (k - j : ℝ), by positivity, ?_⟩
  intro f hf
  have hp : 0 < (j - R : ℝ) := sub_pos.mpr (by exact_mod_cast hRj)
  have hq : 0 < (k - j : ℝ) := sub_pos.mpr (by exact_mod_cast hjk)
  have hsum : (j - R : ℝ) + (k - j : ℝ) = (k - R : ℝ) := by ring
  have h := CNormInterpolation.le_mul_rpow_of_small_scale_bounds
    (CNormInterpolation.cNorm_nonneg s R f)
    (CNormInterpolation.cNorm_mono s f (Nat.le_of_lt (hRj.trans hjk))) hp hq ht₀
    (L := A) (H := A) (X := cNorm s j f) (by
      intro t ht ht1
      simpa only [neg_sub, mul_add, mul_assoc] using hscale f hf t ht ht1)
  simpa only [neg_sub, hsum] using h

/-- Appendix B, `app:lem:elementary-interpolation-jets` and
`app:eq:elementary-interpolation`: interpolation on a closed ball with the exact
exponent `(j - R) / (k - R)`. The constant is uniform over smooth functions.
This is the constructive proof consumed by `cNorm_le_interpolation`, without
completeness or inner-product assumptions. -/
theorem cNorm_le_interpolation_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) {R j k : ℕ} (hRj : R < j) (hjk : j < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) j f ≤
        C * (cNorm (Metric.closedBall x ρ) R f) ^ (1 - (j - R : ℝ) / (k - R)) *
          (cNorm (Metric.closedBall x ρ) k f) ^ ((j - R : ℝ) / (k - R)) := by
  exact cNorm_le_interpolation_of_scale_estimate (Metric.closedBall x ρ) hRj hjk
    (exists_cNorm_scale_estimate x hρ hRj hjk)

end JanetCartan
