module

public import Mathlib.Analysis.ODE.Gronwall

import Mathlib.Tactic.Ring

/-!
# Fixed-time Gronwall estimates

The analytic comparison step in `app:ch_regular_base:lem:buffered-interpolation`.
The constants below separate the low coefficient bound from the single high norm
in the initial value and forcing. No existence theorem for an ODE is assumed here.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: simultaneous scaling of the
initial and forcing bounds scales the Gronwall majorant by the same factor. -/
theorem gronwallBound_mul (δ K ε H T : ℝ) :
    gronwallBound (δ * H) K (ε * H) T = gronwallBound δ K ε T * H := by
  unfold gronwallBound
  split_ifs <;> ring

/-- `app:ch_regular_base:lem:buffered-interpolation`: the fixed-time constant is
nonnegative for nonnegative initial, forcing, coefficient and duration bounds. -/
theorem gronwallBound_nonneg {δ K ε T : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hT : 0 ≤ T) :
    0 ≤ gronwallBound δ K ε T := by
  calc
    0 ≤ δ := hδ
    _ = gronwallBound δ K ε 0 := (gronwallBound_x0 δ K ε).symm
    _ ≤ gronwallBound δ K ε T := gronwallBound_mono hδ hε hK hT

/-- `app:ch_regular_base:lem:buffered-interpolation`: a fixed-time variational
inequality preserves one high coefficient norm `M`. The constant on the right
depends only on `δ`, `K`, `ε` and the interval length, not on `M`. -/
theorem norm_le_oneHigh_of_deriv_bound {u u' : ℝ → E} {a b δ K ε M : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hu : ContinuousOn u (Icc a b))
    (hu' : ∀ t ∈ Ico a b, HasDerivWithinAt u (u' t) (Ici t) t)
    (ha : ‖u a‖ ≤ δ * (1 + M))
    (hbound : ∀ t ∈ Ico a b, ‖u' t‖ ≤ K * ‖u t‖ + ε * (1 + M))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖u t‖ ≤ gronwallBound δ K ε (b - a) * (1 + M) := by
  have hH : 0 ≤ 1 + M := by positivity
  calc
    ‖u t‖ ≤ gronwallBound (δ * (1 + M)) K (ε * (1 + M)) (t - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hu hu' ha hbound t ht
    _ ≤ gronwallBound (δ * (1 + M)) K (ε * (1 + M)) (b - a) :=
      gronwallBound_mono (mul_nonneg hδ hH) (mul_nonneg hε hH) hK
        (sub_le_sub_right ht.2 a)
    _ = gronwallBound δ K ε (b - a) * (1 + M) := gronwallBound_mul ..

/-- `app:ch_regular_base:lem:buffered-interpolation`: the inhomogeneous linear
variational equation `u' = A u + R`, with a bounded low coefficient and forcing
linear in one high norm, has the same one-high bound on the closed interval. -/
theorem norm_le_oneHigh_of_variationalEquation
    {u R : ℝ → E} {A : ℝ → E →L[ℝ] E} {a b δ K ε M : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hu : ContinuousOn u (Icc a b))
    (hu' : ∀ t ∈ Ico a b, HasDerivWithinAt u (A t (u t) + R t) (Ici t) t)
    (ha : ‖u a‖ ≤ δ * (1 + M))
    (hA : ∀ t ∈ Ico a b, ‖A t‖ ≤ K)
    (hR : ∀ t ∈ Ico a b, ‖R t‖ ≤ ε * (1 + M))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖u t‖ ≤ gronwallBound δ K ε (b - a) * (1 + M) := by
  apply norm_le_oneHigh_of_deriv_bound hδ hK hε hM hu hu' ha _ ht
  intro τ hτ
  calc
    ‖A τ (u τ) + R τ‖ ≤ ‖A τ (u τ)‖ + ‖R τ‖ := norm_add_le _ _
    _ ≤ ‖A τ‖ * ‖u τ‖ + ε * (1 + M) :=
      add_le_add ((A τ).le_opNorm _) (hR τ hτ)
    _ ≤ K * ‖u τ‖ + ε * (1 + M) := by
      gcongr
      exact hA τ hτ

/-- `app:ch_regular_base:lem:buffered-interpolation`: homogeneous transport is
bounded by the initial norm times the low-coefficient exponential. -/
theorem norm_le_exp_of_norm_deriv_le {u u' : ℝ → E} {a b K : ℝ}
    (hK : 0 ≤ K) (hu : ContinuousOn u (Icc a b))
    (hu' : ∀ t ∈ Ico a b, HasDerivWithinAt u (u' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, ‖u' t‖ ≤ K * ‖u t‖)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖u t‖ ≤ ‖u a‖ * Real.exp (K * (b - a)) := by
  simpa only [gronwallBound_ε0, add_zero, mul_one, zero_mul] using
    norm_le_oneHigh_of_deriv_bound (δ := ‖u a‖) (ε := 0) (M := 0)
      (norm_nonneg _) hK le_rfl le_rfl hu hu' (by simp)
      (by simpa only [zero_mul, add_zero] using hbound) ht

end JanetCartan
