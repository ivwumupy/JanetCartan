module

public import JanetCartan.Geometry.IsometricEmbedding.Scales

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The two strict normal-comparison exponent gaps

Scalar estimates for `main:eq:canonical-range` and
`app:ch_mean_pairs:eq:mean-stage-normal-errors`, consumed by
`CurrentNormalComparison.norm_current_prefix_sub_original_le`.
-/

@[expose] public noncomputable section

namespace JanetCartan.CurrentNormalComparison

/-- The decay exponent in `H = R^(1+θ)` from the two strict gaps in
`main:eq:canonical-range`. -/
def normalDecayExponent (ε θ β a : ℝ) : ℝ :=
  min ((ε - θ) / 4) (a - 1 - θ - β) / (1 + θ)

/-- The two strict gaps give positive decay in
`app:ch_mean_pairs:eq:mean-stage-normal-errors`. -/
theorem normalDecayExponent_pos {ε θ β a : ℝ} (hθ : 0 ≤ θ)
    (hε : θ < ε) (ha : 1 + θ + β < a) : 0 < normalDecayExponent ε θ β a := by
  unfold normalDecayExponent
  apply div_pos
  · exact lt_min (by linarith) (by linarith)
  · linarith

/-- Absorb the additional prepared-scalar `R⁻ᵃ` term in
`main:eq:canonical-range`. Constants remain independent of prefixes. -/
theorem absorb_prepared_scalar_error {R ε θ β a Cs Cp Cc D : ℝ}
    (hR : 1 ≤ R) (hθβ : 0 ≤ 1 + θ + β)
    (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp) (hCc : 0 ≤ Cc) (hD : 0 ≤ D) :
    Cs * R ^ (-(ε - θ) / 4) + Cp * R ^ (-a + 1 + θ + β) +
        Cc * R ^ (-a + 1 + θ + β) + D * R ^ (-a) ≤
      (Cs + Cp + Cc + D) * (R ^ (-(ε - θ) / 4) + R ^ (-a + 1 + θ + β)) := by
  have hx := Real.rpow_nonneg (by linarith : 0 ≤ R) (-(ε - θ) / 4)
  have hy := Real.rpow_nonneg (by linarith : 0 ≤ R) (-a + 1 + θ + β)
  have hz : R ^ (-a) ≤ R ^ (-a + 1 + θ + β) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hDz := mul_le_mul_of_nonneg_left hz hD
  nlinarith [mul_nonneg hCs hy, mul_nonneg hCp hx, mul_nonneg hCc hx,
    mul_nonneg hD hx]

/-- Convert the two powers of `R` in `main:eq:canonical-range` to one power
of the unchanged ceiling `H = R^(1+θ)`. -/
theorem normal_error_le_ceiling_decay {R H ε θ β a C : ℝ}
    (hR : 1 ≤ R) (hθ : 0 ≤ θ) (hC : 0 ≤ C) (hH : H = R ^ (1 + θ)) :
    C * (R ^ (-(ε - θ) / 4) + R ^ (-a + 1 + θ + β)) ≤
      (2 * C) * H ^ (-normalDecayExponent ε θ β a) := by
  have hden : 1 + θ ≠ 0 := by linarith
  have hexp : (1 + θ) * (-normalDecayExponent ε θ β a) =
      -min ((ε - θ) / 4) (a - 1 - θ - β) := by
    unfold normalDecayExponent
    field_simp
  have hpow : H ^ (-normalDecayExponent ε θ β a) =
      R ^ (-min ((ε - θ) / 4) (a - 1 - θ - β)) := by
    rw [hH, ← Real.rpow_mul (by linarith : 0 ≤ R), hexp]
  have hx : R ^ (-(ε - θ) / 4) ≤ H ^ (-normalDecayExponent ε θ β a) := by
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le hR
    linarith [min_le_left ((ε - θ) / 4) (a - 1 - θ - β)]
  have hy : R ^ (-a + 1 + θ + β) ≤ H ^ (-normalDecayExponent ε θ β a) := by
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le hR
    linarith [min_le_right ((ε - θ) / 4) (a - 1 - θ - β)]
  nlinarith [mul_le_mul_of_nonneg_left hx hC, mul_le_mul_of_nonneg_left hy hC]

/-- The pinned scale windows give a strictly positive comparison exponent in
`main:eq:canonical-range`. -/
theorem fixed_normalDecayExponent_pos :
    0 < normalDecayExponent samplingSlack meanSlack separationExponent carrierExponent :=
  normalDecayExponent_pos (by norm_num [meanSlack])
    (by norm_num [meanSlack, samplingSlack]) scale_windows.2.2.2.1

/-- For the paper's fixed choices, the explicit exponent in `H` is `1/260`
(`main:eq:canonical-range`). -/
theorem fixed_normalDecayExponent_eq :
    normalDecayExponent samplingSlack meanSlack separationExponent carrierExponent = 1 / 260 := by
  norm_num [normalDecayExponent, samplingSlack, meanSlack, separationExponent, carrierExponent]

end JanetCartan.CurrentNormalComparison
