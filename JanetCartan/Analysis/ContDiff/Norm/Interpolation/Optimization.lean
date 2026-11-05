module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Optimizing the interpolation scale

These scalar lemmas implement the optimization in
`app:lem:elementary-interpolation-jets` of paper.tex. They do not assert the
analytic smoothing estimates; those are explicit premises.
-/

public section

open Filter Topology

namespace JanetCartan.CNormInterpolation

/-- Appendix B, `app:lem:elementary-interpolation-jets`: optimize the two smoothing
bounds at scale `(a / b) ^ (1 / (p + q))`. The case `a = 0` follows by a limit. -/
theorem le_mul_rpow_of_scale_bounds {a b X L H p q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hp : 0 < p) (hq : 0 < q)
    (hscale : ∀ t : ℝ, 0 < t → t ≤ 1 → X ≤ L * t ^ (-p) * a + H * t ^ q * b) :
    X ≤ (L + H) * a ^ (1 - p / (p + q)) * b ^ (p / (p + q)) := by
  have hpq : 0 < p + q := add_pos hp hq
  have hθ : p / (p + q) < 1 := (div_lt_one hpq).2 (by linarith)
  rcases ha.eq_or_lt with ha | ha
  · subst a
    have hlim : Tendsto (fun t : ℝ ↦ H * t ^ q * b) (𝓝[>] 0) (𝓝 0) := by
      simpa [Real.zero_rpow hq.ne'] using
        (((Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).const_mul H).mul_const b).tendsto
          |>.mono_left nhdsWithin_le_nhds
    have hX : X ≤ 0 := ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      simpa using hscale t ht.1 ht.2.le)
    simpa [Real.zero_rpow (sub_pos.mpr hθ).ne'] using hX
  · have hb : 0 < b := ha.trans_le hab
    let t := (a / b) ^ (1 / (p + q))
    have ht : 0 < t := Real.rpow_pos_of_pos (div_pos ha hb) _
    have ht1 : t ≤ 1 := Real.rpow_le_one (div_nonneg ha.le hb.le)
      ((div_le_one hb).2 hab) (by positivity)
    have htlow : t ^ (-p) = (a / b) ^ (-(p / (p + q))) := by
      dsimp only [t]
      rw [← Real.rpow_mul (div_nonneg ha.le hb.le)]
      congr 1
      ring
    have hthigh : t ^ q = (a / b) ^ (1 - p / (p + q)) := by
      dsimp only [t]
      rw [← Real.rpow_mul (div_nonneg ha.le hb.le)]
      congr 1
      field_simp
      ring
    have hl : t ^ (-p) * a = a ^ (1 - p / (p + q)) * b ^ (p / (p + q)) := by
      rw [htlow, Real.rpow_neg (div_nonneg ha.le hb.le),
        Real.div_rpow ha.le hb.le, inv_div, Real.rpow_sub ha, Real.rpow_one]
      ring
    have hh : t ^ q * b = a ^ (1 - p / (p + q)) * b ^ (p / (p + q)) := by
      rw [hthigh, Real.div_rpow ha.le hb.le, Real.rpow_sub hb, Real.rpow_one]
      field_simp
    calc
      X ≤ L * t ^ (-p) * a + H * t ^ q * b := hscale t ht ht1
      _ = (L + H) * a ^ (1 - p / (p + q)) * b ^ (p / (p + q)) := by
        rw [mul_assoc L, mul_assoc H, hl, hh]
        ring

/-- Appendix B, `app:lem:elementary-interpolation-jets`: the same optimization for
estimates available only for `0 < t ≤ t₀`. Rescaling changes only the constant. -/
theorem le_mul_rpow_of_small_scale_bounds {a b X L H p q t₀ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hp : 0 < p) (hq : 0 < q) (ht₀ : 0 < t₀)
    (hscale : ∀ t : ℝ, 0 < t → t ≤ t₀ → X ≤ L * t ^ (-p) * a + H * t ^ q * b) :
    X ≤ (L * t₀ ^ (-p) + H * t₀ ^ q) *
      a ^ (1 - p / (p + q)) * b ^ (p / (p + q)) := by
  apply le_mul_rpow_of_scale_bounds ha hab hp hq
  intro t ht ht1
  calc
    X ≤ L * (t₀ * t) ^ (-p) * a + H * (t₀ * t) ^ q * b :=
      hscale (t₀ * t) (mul_pos ht₀ ht) (mul_le_of_le_one_right ht₀.le ht1)
    _ = (L * t₀ ^ (-p)) * t ^ (-p) * a + (H * t₀ ^ q) * t ^ q * b := by
      rw [Real.mul_rpow ht₀.le ht.le, Real.mul_rpow ht₀.le ht.le]
      ring

end JanetCartan.CNormInterpolation
