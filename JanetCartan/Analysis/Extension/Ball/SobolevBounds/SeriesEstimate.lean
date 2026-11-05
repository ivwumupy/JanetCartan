module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.CollarIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Summation of squared collar estimates

A weighted Cauchy–Schwarz inequality and dominated convergence implement the
series argument following `app:ch_regular_base:eq:extension-collar-l2`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.BallExtension

/-- Weighted finite Cauchy–Schwarz for the series in
`app:ch_regular_base:eq:extension-collar-l2`. The geometric weights have sum at
most two, independently of the number of terms. -/
theorem norm_sum_sq_le_two_mul_weighted_sum {F : Type*} [NormedAddCommGroup F]
    (v : ℕ → F) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, v k‖ ^ 2 ≤
      2 * ∑ k ∈ Finset.range N, (2 : ℝ) ^ k * ‖v k‖ ^ 2 := by
  calc
    _ ≤ (∑ k ∈ Finset.range N, ‖v k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (∑ k ∈ Finset.range N, (1 / (2 : ℝ)) ^ k) *
        ∑ k ∈ Finset.range N, (2 : ℝ) ^ k * ‖v k‖ ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range N)
        (fun _ _ ↦ by positivity) (fun _ _ ↦ by positivity)
      intro k _
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_geometric_two_le N)
      (Finset.sum_nonneg (fun _ _ ↦ by positivity))

/-- The integrated infinite-series estimate used after
`app:ch_regular_base:eq:extension-collar-l2`. Uniform absolute convergence is
used only to justify passage to the integral; the bound comes from the squared
integrals and is independent of the uniform majorant. -/
theorem integral_sq_norm_tsum_le_weighted_bound
    {X F : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {v : ℕ → X → F} {u b : ℕ → ℝ}
    (hv : ∀ k, AEStronglyMeasurable (v k) μ)
    (hu : Summable u) (hu0 : ∀ k, 0 ≤ u k)
    (hvu : ∀ k, ∀ᵐ x ∂μ, ‖v k x‖ ≤ u k)
    (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (hvb : ∀ k, (2 : ℝ) ^ k * (∫ x, ‖v k x‖ ^ 2 ∂μ) ≤ b k) :
    (∫ x, ‖∑' k, v k x‖ ^ 2 ∂μ) ≤ 2 * ∑' k, b k := by
  have hvi (k : ℕ) : Integrable (fun x ↦ ‖v k x‖ ^ 2) μ :=
    (integrable_const (u k ^ 2)).mono' ((hv k).norm.pow 2) (by
      filter_upwards [hvu k] with x hx
      simpa only [norm_pow, norm_norm] using
        pow_le_pow_left₀ (norm_nonneg _) hx 2)
  have hpartial (N : ℕ) : ∀ᵐ x ∂μ, ‖∑ k ∈ Finset.range N, v k x‖ ≤ ∑' k, u k := by
    filter_upwards [ae_all_iff.mpr hvu] with x hx
    exact (norm_sum_le_of_le _ (fun k _ ↦ hx k)).trans
      (hu.sum_le_tsum _ (fun k _ ↦ hu0 k))
  have hpi (N : ℕ) : Integrable (fun x ↦ ‖∑ k ∈ Finset.range N, v k x‖ ^ 2) μ :=
    (integrable_const ((∑' k, u k) ^ 2)).mono'
      ((Finset.aestronglyMeasurable_fun_sum _ (fun k _ ↦ hv k)).norm.pow 2) (by
        filter_upwards [hpartial N] with x hx
        simpa only [norm_pow, norm_norm] using
          pow_le_pow_left₀ (norm_nonneg _) hx 2)
  have hbound (N : ℕ) : (∫ x, ‖∑ k ∈ Finset.range N, v k x‖ ^ 2 ∂μ) ≤
      2 * ∑' k, b k := by
    calc
      _ ≤ ∫ x, 2 * ∑ k ∈ Finset.range N, (2 : ℝ) ^ k * ‖v k x‖ ^ 2 ∂μ :=
        integral_mono_ae (hpi N)
          ((integrable_finsetSum _ (fun k _ ↦ (hvi k).const_mul _)).const_mul _)
          (ae_of_all _ (fun x ↦ norm_sum_sq_le_two_mul_weighted_sum (fun k ↦ v k x) N))
      _ = 2 * ∑ k ∈ Finset.range N, (2 : ℝ) ^ k * (∫ x, ‖v k x‖ ^ 2 ∂μ) := by
        rw [integral_const_mul, integral_finsetSum _ (fun k _ ↦ (hvi k).const_mul _)]
        simp_rw [integral_const_mul]
      _ ≤ 2 * ∑ k ∈ Finset.range N, b k := by gcongr with k; exact hvb k
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb.sum_le_tsum _ (fun k _ ↦ hb0 k)) (by norm_num)
  have hlim : Tendsto (fun N ↦ ∫ x, ‖∑ k ∈ Finset.range N, v k x‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ x, ‖∑' k, v k x‖ ^ 2 ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall (fun N ↦ (hpi N).aestronglyMeasurable)
    · refine ⟨(∑' k, u k) ^ 2, Eventually.of_forall ?_⟩
      intro N
      filter_upwards [hpartial N] with x hx
      simpa only [norm_pow, norm_norm] using
        pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [ae_all_iff.mpr hvu] with x hx
      exact ((hu.of_norm_bounded hx).tendsto_sum_tsum_nat.norm).pow 2
  exact le_of_tendsto hlim (Eventually.of_forall hbound)

end JanetCartan.BallExtension
