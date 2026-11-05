module

public import JanetCartan.Analysis.Iteration.AdaptiveSchedule
public import JanetCartan.Analysis.Iteration.SmoothLimit.Rates
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Summability along one adaptive schedule

The numerical passage from `main:eq:staircase` to `main:eq:final-Cr` in Section 9.
All derivative orders use the same schedule. The actual increment estimates are
explicit inputs; no correction sequence is asserted to exist here.
-/

@[expose] public noncomputable section

open scoped Topology
open Filter

namespace JanetCartan

/-- `main:eq:final-Cr`: every fixed derivative loss is summable along the single
adaptive staircase, without any growth restriction on its finite thresholds. -/
theorem summable_powerAdaptiveSchedule_bound (H : ℕ → ℝ) (k₀ : ℕ)
    {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v) (b : ℝ) :
    Summable (fun j ↦ iterationScale R₀ v j ^
      (-(powerAdaptiveSchedule H R₀ v k₀ j : ℝ) + b)) := by
  apply summable_rpow_order_bound _ (summable_inverse_power_scale hR₀ hv)
    (powerAdaptiveSchedule_tendsto_atTop H k₀ hR₀ hv) b
  intro j
  exact Real.one_le_rpow hR₀.le (pow_nonneg (by linarith) j)

/-- `main:eq:metric-induction`: the prescribed squared metric budgets tend to zero
for the same staircase used for every derivative order. -/
theorem tendsto_powerAdaptiveSchedule_metricBudget (H : ℕ → ℝ) (k₀ : ℕ)
    {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v) :
    Tendsto (fun j ↦ (iterationScale R₀ v j ^
      (-(powerAdaptiveSchedule H R₀ v k₀ j : ℝ))) ^ 2) atTop (𝓝 0) := by
  have hs : Summable (fun j ↦ iterationScale R₀ v j ^
      (-(powerAdaptiveSchedule H R₀ v k₀ j : ℝ))) := by
    simpa only [add_zero] using summable_powerAdaptiveSchedule_bound H k₀ hR₀ hv 0
  simpa only [zero_pow (by decide : 2 ≠ 0)] using hs.tendsto_atTop_zero.pow 2

/-- `main:eq:final-Cr`: the actual compact derivative seminorms are simultaneously
summable for every fixed order, conditional on the displayed increment estimates.
The constants and the start of each bound may depend on the derivative order;
the increments, domain, initial scale, and adaptive schedule do not. -/
theorem summable_cNorm_of_powerAdaptiveSchedule_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : ℕ → ℝ) (k₀ : ℕ) {R₀ v : ℝ} (hR₀ : 1 < R₀) (hv : 1 < v)
    {s : Set E} {u : ℕ → E → F} {C b : ℕ → ℝ}
    (hbound : ∀ r, ∀ᶠ j in atTop, cNorm s r (u j) ≤ C r *
      iterationScale R₀ v j ^ (-(powerAdaptiveSchedule H R₀ v k₀ j : ℝ) + b r)) :
    ∀ r, Summable (fun j ↦ cNorm s r (u j)) := by
  intro r
  apply Summable.of_norm_bounded_eventually
    ((summable_powerAdaptiveSchedule_bound H k₀ hR₀ hv (b r)).mul_left (C r))
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound r] with j hj
  simpa only [Real.norm_eq_abs, abs_of_nonneg (cNorm_nonneg s r (u j))] using hj

end JanetCartan
