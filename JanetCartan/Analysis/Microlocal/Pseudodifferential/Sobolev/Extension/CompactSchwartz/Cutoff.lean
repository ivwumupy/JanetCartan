module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Expanding smooth cutoffs

The cutoff construction for compact-test approximation in
`app:ch_regular_base:eq:fio-input`. Its consumer is the Fourier Sobolev
approximation theorem in `Extension.CompactSchwartz`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology ContDiff

namespace JanetCartan.Pseudodifferential.CompactSchwartz

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private def bump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

private def scale (j : ℕ) : ℝ := ((j : ℝ) + 1)⁻¹

private theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

private theorem scale_le_one (j : ℕ) : scale j ≤ 1 := by
  unfold scale
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])

private def cutoff (j : ℕ) (x : E) : ℝ := bump (scale j • x)

private theorem cutoff_smooth (j : ℕ) : ContDiff ℝ ∞ (cutoff (d := d) j) :=
  bump.contDiff.comp (contDiff_id.const_smul _)

private theorem cutoff_compact (j : ℕ) : HasCompactSupport (cutoff (d := d) j) := by
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 (scale j) (scale_pos j).ne')
  exact bump.hasCompactSupport.comp_homeomorph e.toHomeomorph

/-- Smooth compact truncations for `app:ch_regular_base:eq:fio-input`. -/
@[no_expose] def truncate (f : 𝓢(E, ℂ)) (j : ℕ) : 𝓢(E, ℂ) :=
  ((cutoff_compact j).smul_right (f' := (f : E → ℂ))).toSchwartzMap
    ((cutoff_smooth j).smul (f.smooth ⊤))

/-- The truncations in `app:ch_regular_base:eq:fio-input` have compact support. -/
theorem truncate_hasCompactSupport (f : 𝓢(E, ℂ)) (j : ℕ) :
    HasCompactSupport (truncate f j : E → ℂ) :=
  (cutoff_compact j).smul_right

private theorem cutoff_derivative_bound (j i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (cutoff j) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i ((bump (d := d)).hasCompactSupport.toSchwartzMap bump.contDiff) := by
  change ‖iteratedFDeriv ℝ i (fun y : E ↦ bump (scale j • y)) x‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul _ bump.contDiff]
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (scale_pos j).le _)]
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ i (bump (d := d)) (scale j • x)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ (scale_pos j).le (scale_le_one j)) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact ((bump (d := d)).hasCompactSupport.toSchwartzMap bump.contDiff).norm_iteratedFDeriv_le_seminorm ℝ i (scale j • x)

private def bound (f : 𝓢(E, ℂ)) (k n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i ((bump (d := d)).hasCompactSupport.toSchwartzMap bump.contDiff) *
    SchwartzMap.seminorm ℝ k (n - i) f) + SchwartzMap.seminorm ℝ k n f

private theorem bound_nonneg (f : 𝓢(E, ℂ)) (k n : ℕ) : 0 ≤ bound f k n := by
  unfold bound
  positivity

private theorem weighted_error_bound (f : 𝓢(E, ℂ)) (j k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (truncate f j - f) x‖ ≤ bound f k n := by
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((truncate f j : E → ℂ) - (f : E → ℂ)) x‖ ≤ _
  rw [iteratedFDeriv_sub ((truncate f j).smooth n) (f.smooth n)]
  refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
  rw [mul_add]
  apply add_le_add _ (f.le_seminorm ℝ k n x)
  have h := norm_iteratedFDeriv_smul_le (cutoff_smooth (d := d) j) (f.smooth ⊤) x (n := n) (by simp)
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoff j) x‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
    _ ≤ _ := by
      gcongr
      · exact cutoff_derivative_bound j i x
      · exact f.le_seminorm ℝ k (n - i) x

private theorem error_locally_zero (f : 𝓢(E, ℂ)) (j : ℕ) {x : E}
    (hx : ‖x‖ < (j : ℝ) + 1) : (truncate f j - f : 𝓢(E, ℂ)) =ᶠ[𝓝 x] (0 : E → ℂ) := by
  have hc : cutoff j =ᶠ[𝓝 x] (1 : E → ℝ) := by
    have hmem : scale j • x ∈ Metric.ball (0 : E) (bump (d := d)).rIn := by
      change dist (scale j • x) 0 < 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (scale_pos j).le]
      change ((j : ℝ) + 1)⁻¹ * ‖x‖ < 1
      rw [inv_mul_lt_iff₀ (by positivity)]
      simpa using hx
    exact (bump.eventuallyEq_one_of_mem_ball hmem).comp_tendsto
      ((continuous_const_smul (scale j)).tendsto x)
  filter_upwards [hc] with y hy
  change cutoff j y • f y - f y = 0
  rw [hy, Pi.one_apply, one_smul, sub_self]

private theorem seminorm_error_le (f : 𝓢(E, ℂ)) (j k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (truncate f j - f) ≤ bound f (k + 1) n / ((j : ℝ) + 1) := by
  apply SchwartzMap.seminorm_le_bound _ _ _ _ (div_nonneg (bound_nonneg _ _ _) (by positivity))
  intro x
  by_cases hx : ‖x‖ < (j : ℝ) + 1
  · rw [((error_locally_zero f j hx).iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero, mul_zero]
    exact div_nonneg (bound_nonneg _ _ _) (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    calc
      _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (truncate f j - f) x‖) * ‖x‖ := by
        gcongr
        exact le_of_not_gt hx
      _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n (truncate f j - f) x‖ := by ring
      _ ≤ _ := weighted_error_bound f j (k + 1) n x

/-- Expanding smooth cutoffs converge in every Schwartz seminorm, supplying
actual compact-test approximation for `app:ch_regular_base:eq:fio-input`. -/
theorem tendsto_truncate (f : 𝓢(E, ℂ)) : Tendsto (truncate f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  have ht : Tendsto (fun j : ℕ ↦ bound f (k + 1) n / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (bound f (k + 1) n)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
  exact (seminorm_error_le f j k n).trans_lt hj

end JanetCartan.Pseudodifferential.CompactSchwartz
