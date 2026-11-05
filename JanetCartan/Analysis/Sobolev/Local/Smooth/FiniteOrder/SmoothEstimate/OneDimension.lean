module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Jets
public import JanetCartan.Analysis.Sobolev.Local.Embedding.SmoothOneDimension

/-!
# Uniform smooth L² jet bounds in dimension one

For the norms in `app:not:fourier`, the real-line pointwise H¹ estimate and
scalar-to-jet lifting prove the one-dimensional smooth estimate used in
`app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The scalar pointwise estimate with two derivatives on the real line,
transported to one-dimensional Euclidean space. This supplies the scalar
input to the jet estimate for `app:ch_regular:thm:exact-correction`. -/
theorem smooth_scalar_pointwise_estimate_one_dimension
    {v : EuclideanSpace ℝ (Fin 1) → ℝ} (hv : ContDiff ℝ ∞ v)
    (hmem : ∀ l ≤ 2, MemLp (iteratedFDeriv ℝ l v) 2 volume)
    (x : EuclideanSpace ℝ (Fin 1)) :
    ‖v x‖ ≤ ∑ l ∈ Finset.range (2 + 1),
      (eLpNorm (iteratedFDeriv ℝ l v) 2 volume).toReal := by
  have hzero : eLpNorm v 2 volume = eLpNorm (iteratedFDeriv ℝ 0 v) 2 volume :=
    eLpNorm_congr_norm_ae hv.continuous.aestronglyMeasurable
      (hv.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y ↦ (norm_iteratedFDeriv_zero).symm))
  have h := enorm_le_eLpNorm_two_add_iteratedFDeriv_one_dimension
    (hv.of_le (by norm_num)) x
  rw [hzero] at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(hmem 0 (by omega)).ne_top, (hmem 1 (by omega)).ne_top⟩) h
  rw [toReal_enorm, ENNReal.toReal_add (hmem 0 (by omega)).ne_top
    (hmem 1 (by omega)).ne_top] at hreal
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
    hreal.trans (le_add_of_nonneg_right (ENNReal.toReal_nonneg))

/-- The uniform smooth L² jet estimate in dimension one, with constant `1`
and the derivative budget `k + n + 1` required by the finite-order regularity
argument in `app:ch_regular:thm:exact-correction`. The function need not have
compact support or satisfy any additional decay condition. -/
theorem exists_smooth_jet_estimate_one_dimension (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : EuclideanSpace ℝ (Fin 1) → F,
      ContDiff ℝ ∞ v →
      (∀ l ≤ k + 1 + 1, MemLp (iteratedFDeriv ℝ l v) 2 volume) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j v x‖ ≤
        C * ∑ l ∈ Finset.range (k + 1 + 1 + 1),
          (eLpNorm (iteratedFDeriv ℝ l v) 2 volume).toReal := by
  refine ⟨1, zero_le_one, ?_⟩
  intro v hv hmem j hj x
  apply smooth_jet_estimate_of_scalar (r := 2) volume zero_le_one
      (fun u hu humem y ↦ ?_) hv (fun l hl ↦ hmem l (by omega)) hj x
  simpa only [one_mul] using smooth_scalar_pointwise_estimate_one_dimension hu humem y

end JanetCartan.LocalSobolev.FiniteOrder
