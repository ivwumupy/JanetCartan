module

public import JanetCartan.Analysis.Operator.CanonicalRow

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Canonical estimates from a normal comparison

This is the Hilbert-space step in `main:prop:canonical`: a comparison of the
complete normal with the reference normal bounds the canonical adjoint. The
nonnegative auxiliary summand is retained. The comparison, raw estimates, and
continuum inverse are explicit inputs, not constructions of the actual waves.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace JanetCartan.CanonicalChange

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The auxiliary normal is nonnegative (`main:prop:canonical`). This applies
to the composite auxiliary row `A₀ π_K`, with its original raw adjoint. -/
theorem auxiliary_normal_nonneg (T : E →L[ℝ] F) (q : F) :
    0 ≤ inner ℝ ((T.comp T.adjoint) q) q := by
  rw [comp_apply, ← adjoint_inner_right, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

/-- `main:eq:canonical-range` bounds the carrier adjoint even though the
comparison concerns the complete output, including the auxiliary summand. -/
theorem adjoint_norm_sq_le_of_normal_comparison
    (A : E →L[ℝ] F) (auxiliary reference : F →L[ℝ] F)
    {M ε : ℝ} (hauxiliary : ∀ q, 0 ≤ inner ℝ (auxiliary q) q)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖auxiliary + A.comp A.adjoint - reference‖ ≤ ε) (q : F) :
    ‖A.adjoint q‖ ^ 2 ≤ (M + ε) * ‖q‖ ^ 2 := by
  have hnormal : inner ℝ (A (A.adjoint q)) q = ‖A.adjoint q‖ ^ 2 := by
    rw [← adjoint_inner_right, real_inner_self_eq_norm_sq]
  have href : inner ℝ (reference q) q ≤ M * ‖q‖ ^ 2 := by
    calc
      inner ℝ (reference q) q ≤ ‖reference q‖ * ‖q‖ := real_inner_le_norm _ _
      _ ≤ (M * ‖q‖) * ‖q‖ := by
        gcongr
        exact (reference.le_opNorm q).trans
          (mul_le_mul_of_nonneg_right hreference (norm_nonneg q))
      _ = M * ‖q‖ ^ 2 := by ring
  have herr : inner ℝ ((auxiliary + A.comp A.adjoint - reference) q) q ≤
      ε * ‖q‖ ^ 2 := by
    calc
      inner ℝ ((auxiliary + A.comp A.adjoint - reference) q) q ≤
          ‖(auxiliary + A.comp A.adjoint - reference) q‖ * ‖q‖ :=
        real_inner_le_norm _ _
      _ ≤ (ε * ‖q‖) * ‖q‖ := by
        gcongr
        exact ((auxiliary + A.comp A.adjoint - reference).le_opNorm q).trans
          (mul_le_mul_of_nonneg_right hcomparison (norm_nonneg q))
      _ = ε * ‖q‖ ^ 2 := by ring
  simp only [sub_apply, add_apply, comp_apply, inner_sub_left, inner_add_left] at herr
  rw [hnormal] at herr
  nlinarith [hauxiliary q]

/-- The bounded-row consequence used in `main:prop:canonical`. The reference
normal and comparison error, rather than individual sample weights, control it. -/
theorem row_norm_le_of_normal_comparison
    (A : E →L[ℝ] F) (auxiliary reference : F →L[ℝ] F)
    {M ε : ℝ} (hauxiliary : ∀ q, 0 ≤ inner ℝ (auxiliary q) q)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖auxiliary + A.comp A.adjoint - reference‖ ≤ ε) :
    ‖A‖ ≤ Real.sqrt (M + ε) := by
  have hnonneg : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  rw [← LinearIsometryEquiv.norm_map adjoint A]
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro q
  have h := adjoint_norm_sq_le_of_normal_comparison A auxiliary reference
    hauxiliary hreference hcomparison q
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hnonneg] using h

variable {ι : Type*} [Fintype ι]
variable {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
  [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- Squaring the raw estimates before summation gives the weighted bounds of
`app:ch_mean_pairs:eq:mean-canonical-weighted-low` and
`app:ch_mean_pairs:eq:mean-canonical-weighted-C`. The size can include the fixed
observation cutoff. The comparison and raw estimates remain explicit premises. -/
theorem sum_weighted_size_sq_le_of_normal_comparison
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (A : ∀ i, Raw i →L[ℝ] F)
    (auxiliary reference Q : F →L[ℝ] F) (size : ∀ i, Raw i → ℝ)
    {M ε c : ℝ} (hc : 0 ≤ c)
    (hauxiliary : ∀ q, 0 ≤ inner ℝ (auxiliary q) q)
    (hreference : ‖reference‖ ≤ M)
    (hcomparison : ‖auxiliary + (CanonicalRow.weightedRow μ A).comp
      (CanonicalRow.weightedRow μ A).adjoint - reference‖ ≤ ε)
    (hraw : ∀ i v, size i v ^ 2 ≤ c * ‖v‖ ^ 2) (r : F) :
    ∑ i, μ i * size i ((A i).adjoint (Q r)) ^ 2 ≤
      c * (M + ε) * ‖Q‖ ^ 2 * ‖r‖ ^ 2 := by
  have hnonneg : 0 ≤ M + ε := add_nonneg ((norm_nonneg _).trans hreference)
    ((norm_nonneg _).trans hcomparison)
  have hQ : ‖Q r‖ ^ 2 ≤ ‖Q‖ ^ 2 * ‖r‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (Q.le_opNorm r)
  calc
    ∑ i, μ i * size i ((A i).adjoint (Q r)) ^ 2 ≤
        c * ‖(CanonicalRow.weightedRow μ A).adjoint (Q r)‖ ^ 2 :=
      CanonicalRow.sum_weighted_size_sq_le_adjoint μ hμ A size hraw (Q r)
    _ ≤ c * ((M + ε) * ‖Q r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (adjoint_norm_sq_le_of_normal_comparison
        _ auxiliary reference hauxiliary hreference hcomparison (Q r)) hc
    _ ≤ c * ((M + ε) * (‖Q‖ ^ 2 * ‖r‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hnonneg) hc
    _ = c * (M + ε) * ‖Q‖ ^ 2 * ‖r‖ ^ 2 := by ring

/-- The individual estimates of `app:ch_mean_pairs:eq:mean-canonical-bounds`
use the component operator norm on the initial raw Hilbert space. This transfer
also applies to the Fourier L¹ size of the unmultiplied initial datum. -/
theorem size_adjoint_inverse_le (A : E →L[ℝ] F) (Q : F →L[ℝ] F)
    (size : E → ℝ) {c a : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ a)
    (hraw : ∀ v, size v ≤ c * ‖v‖) (r : F) :
    size (A.adjoint (Q r)) ≤ c * a * ‖Q‖ * ‖r‖ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hA
  calc
    size (A.adjoint (Q r)) ≤ c * ‖A.adjoint (Q r)‖ := hraw _
    _ ≤ c * (a * ‖Q r‖) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply (A.adjoint.le_opNorm _).trans
      exact mul_le_mul_of_nonneg_right
        (by simpa only [LinearIsometryEquiv.norm_map] using hA) (norm_nonneg _)
    _ ≤ c * (a * (‖Q‖ * ‖r‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Q.le_opNorm r) ha) hc
    _ = c * a * ‖Q‖ * ‖r‖ := by ring

end JanetCartan.CanonicalChange
