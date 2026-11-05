module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The three radial regions of the reverse complement

The scalar estimates used by `reverseSource_gap_uniform` for the complete
complement in `app:ch_response:thm:response-literal-transfer`. The map `F` will
be the physical source gradient `S_x(x, ·)`. The inverse estimate is required on
**all** of `D`, including angular and radial shoulders, not just near the carrier.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

/-- A uniform constant for the reverse complement in
`app:ch_response:thm:response-literal-transfer`. Here `R` is the large-radius
threshold, `a` the central lower bound, `m` the annular lower bound, and `L`
the full inverse-chart Lipschitz constant. -/
def reverseGapConstant (a m L c R : ℝ) : ℝ :=
  min (a / 4) (min (m / 4) (c / (L * (1 + R))))

/-- Positivity of the constant used by `reverseSource_gap_of_chart_bounds`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem reverseGapConstant_pos {a m L c R : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hL : 0 < L) (hc : 0 < c) (hR : 1 ≤ R) :
    0 < reverseGapConstant a m L c R := by
  unfold reverseGapConstant
  positivity

/-- The complete reverse-source gap, before specializing `F` to `S_x`, in
`app:ch_response:thm:response-literal-transfer`. Small and large radii use
annular bounds; comparable radii use the full inverse chart. The perturbation
`θ` is a physical covector. Equality at the selector boundary is allowed. -/
theorem reverseSource_gap_of_chart_bounds {n : ℕ}
    {F : Euclidean n → Euclidean n} {D : Set (Euclidean n)}
    {a b m M L c R ρ : ℝ} {ζ η θ : Euclidean n}
    (ha : 0 < a) (hm : 0 < m) (hL : 0 < L) (hc : 0 < c)
    (hR : 1 ≤ R) (hbR : 2 * b ≤ m * R) (hρ : 0 < ρ)
    (hζ : ρ • ζ ∈ D) (hη : η ∈ D)
    (hhom : F (ρ • ζ) = ρ • F ζ)
    (hcentral : a ≤ ‖F ζ‖ ∧ ‖F ζ‖ ≤ b)
    (hannular : m * ‖η‖ ≤ ‖F η‖ ∧ ‖F η‖ ≤ M * ‖η‖)
    (hinverse : ∀ u ∈ D, ∀ v ∈ D, ‖u - v‖ ≤ L * ‖F u - F v‖)
    (hfar : c * ρ ≤ ‖η - ρ • ζ‖)
    (hθ : ‖θ‖ ≤ (reverseGapConstant a m L c R / 2) * ρ) :
    (reverseGapConstant a m L c R / 2) * (ρ + ‖η‖) ≤
      ‖ρ • F ζ - F η + θ‖ := by
  let d := reverseGapConstant a m L c R
  have hd : 0 < d := reverseGapConstant_pos ha hm hL hc hR
  have hda : d ≤ a / 4 := min_le_left _ _
  have hdm : d ≤ m / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdc : d * (L * (1 + R)) ≤ c := by
    apply (le_div_iff₀ (by positivity : 0 < L * (1 + R))).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hnorm : ‖ρ • F ζ‖ = ρ * ‖F ζ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  have hlow := norm_sub_norm_le (ρ • F ζ) (F η)
  have hhigh := norm_sub_norm_le (F η) (ρ • F ζ)
  rw [hnorm] at hlow hhigh
  rw [norm_sub_rev (F η)] at hhigh
  have hcentralLo : a * ρ ≤ ρ * ‖F ζ‖ := by nlinarith [hcentral.1]
  have hcentralHi : ρ * ‖F ζ‖ ≤ b * ρ := by nlinarith [hcentral.2]
  have hbase : d * (ρ + ‖η‖) ≤ ‖ρ • F ζ - F η‖ := by
    by_cases hsmall : ‖η‖ ≤ ρ ∧ 2 * M * ‖η‖ ≤ a * ρ
    · -- Small radial region: the central covector dominates.
      have hscale : d * (ρ + ‖η‖) ≤ (a / 4) * (2 * ρ) :=
        (mul_le_mul_of_nonneg_left (by linarith [hsmall.1]) hd.le).trans
          (mul_le_mul_of_nonneg_right hda (by positivity))
      nlinarith [hannular.2, hsmall.2]
    · by_cases hlarge : R * ρ ≤ ‖η‖
      · -- Large radial region: the annular lower bound dominates.
        have hηρ : ρ ≤ ‖η‖ := by nlinarith
        have hbη : 2 * b * ρ ≤ m * ‖η‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hbR hρ.le,
            mul_le_mul_of_nonneg_left hlarge hm.le]
        have hscale : d * (ρ + ‖η‖) ≤ (m / 4) * (2 * ‖η‖) :=
          (mul_le_mul_of_nonneg_left (by linarith) hd.le).trans
            (mul_le_mul_of_nonneg_right hdm (by positivity))
        nlinarith [hannular.1]
      · -- Comparable radial region: use the entire buffered inverse chart.
        have hinv := hinverse (ρ • ζ) hζ η hη
        rw [hhom, norm_sub_rev (ρ • ζ)] at hinv
        have hscale : d * (ρ + ‖η‖) ≤ d * ((1 + R) * ρ) := by
          apply mul_le_mul_of_nonneg_left _ hd.le
          nlinarith
        have hmul : L * (d * ((1 + R) * ρ)) ≤ c * ρ := by
          nlinarith [mul_le_mul_of_nonneg_right hdc hρ.le]
        nlinarith
  have hpert := norm_sub_norm_le (ρ • F ζ - F η) (-θ)
  rw [norm_neg, sub_neg_eq_add] at hpert
  change ‖θ‖ ≤ d / 2 * ρ at hθ
  change d / 2 * (ρ + ‖η‖) ≤ _
  nlinarith [mul_nonneg hd.le (norm_nonneg η)]

end JanetCartan.ResponseTransfer
