module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite depth for arbitrary accuracy

Scalar estimates used in `app:ch_regular:eq:finite-observation`.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- The scale calculation in `app:ch_regular:eq:finite-observation`:
the observation loses `c` powers and the target input order loses `t`, while
each smoothing step gains `σ` powers. -/
theorem finite_neumann_scale_bound {ρ L σ c : ℝ} (hρ : 1 ≤ ρ)
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hscale : L ≤ ρ ^ (1 - σ)) (t N : ℕ) :
    ρ ^ c * L ^ t * (L / ρ) ^ N ≤ ρ ^ (c + (t : ℝ) - σ * N) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hLρ : L ≤ ρ := by
    calc
      L ≤ ρ ^ (1 - σ) := hscale
      _ ≤ ρ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (by linarith)
      _ = ρ := Real.rpow_one ρ
  have hratio : L / ρ ≤ ρ ^ (-σ) := by
    calc
      L / ρ ≤ ρ ^ (1 - σ) / ρ := div_le_div_of_nonneg_right hscale hρpos.le
      _ = ρ ^ ((1 - σ) - 1) := by
        simpa only [Real.rpow_one] using (Real.rpow_sub hρpos (1 - σ) 1).symm
      _ = ρ ^ (-σ) := by congr 1; ring
  calc
    ρ ^ c * L ^ t * (L / ρ) ^ N ≤ ρ ^ c * ρ ^ t * (ρ ^ (-σ)) ^ N := by
      gcongr
    _ = ρ ^ (c + (t : ℝ) - σ * N) := by
      rw [← Real.rpow_natCast ρ t, ← Real.rpow_natCast (ρ ^ (-σ)) N,
        ← Real.rpow_mul hρpos.le, ← Real.rpow_add hρpos, ← Real.rpow_add hρpos]
      congr 1
      ring

/-- Choose the integer smoothing order before the frequency in
`app:ch_regular:eq:finite-observation`. The resulting depth is `N + t`. -/
theorem exists_finite_neumann_order {σ : ℝ} (hσ : 0 < σ) (c Q : ℝ) (t : ℕ) :
    ∃ N : ℕ, 0 < N ∧ c + (t : ℝ) - σ * N ≤ -Q := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 ((c + (t : ℝ) + Q) / σ))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNlarge := lt_of_le_of_lt (le_max_right _ _) hN
  have hmul := (div_lt_iff₀ hσ).mp hNlarge
  refine ⟨N, by exact_mod_cast hNpos, ?_⟩
  linarith

end JanetCartan
