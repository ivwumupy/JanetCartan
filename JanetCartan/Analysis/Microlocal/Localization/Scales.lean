module

public import JanetCartan.Geometry.IsometricEmbedding.Scales

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorption of the nonstationary tail

The scale arithmetic in `app:ch_osc:eq:osc-source-negative`. These results
do not supply the analytic shell estimate. In particular the integration order
may depend on the requested Sobolev order, but the scale gap is fixed.
-/

@[expose] public noncomputable section

namespace JanetCartan.Localization

/-- `app:ch_osc:eq:osc-source-negative`: choose an integer integration order
above the integrability threshold and large enough for any desired gain. -/
theorem exists_tail_order {σ : ℝ} (hσ : 0 < σ) (d M : ℝ) :
    ∃ q : ℕ, d < q ∧ M + d ≤ σ * q := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max d ((M + d) / σ))
  refine ⟨q, (le_max_left _ _).trans_lt hq, ?_⟩
  have h := (div_lt_iff₀ hσ).mp ((le_max_right _ _).trans_lt hq)
  linarith

/-- `app:ch_osc:eq:osc-source-negative`: the loss `ρ^d` is absorbed by repeated
integration by parts whenever `σ q ≥ M+d`. Here `d=n/2` in the source. -/
theorem tail_factor_le_negative_power {ρ L σ d M : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hgap : L ≤ ρ ^ (1 - σ))
    (hq : M + d ≤ σ * q) :
    ρ ^ d * (L / ρ) ^ q ≤ ρ ^ (-M) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hratio : L / ρ ≤ ρ ^ (-σ) := by
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub hρpos, Real.rpow_one]
    exact div_le_div_of_nonneg_right hgap hρpos.le
  calc
    ρ ^ d * (L / ρ) ^ q ≤ ρ ^ d * (ρ ^ (-σ)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio q)
        (Real.rpow_nonneg hρpos.le _)
    _ = ρ ^ (d - σ * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρpos.le, ← Real.rpow_add hρpos]
      congr 1
      ring
    _ ≤ ρ ^ (-M) := Real.rpow_le_rpow_of_exponent_le hρ (by linarith)

/-- `app:ch_osc:eq:osc-source-negative`: the last arithmetic step after an
annular split. `B` includes the fixed amplitude, total variation and `L^b`.
The displayed split bound is an explicit analytic input, not a proved norm
estimate for the source. -/
theorem negative_bound_of_annular_split {ρ L σ d M B N : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hgap : L ≤ ρ ^ (1 - σ))
    (hq : M + d ≤ σ * q) (hB : 0 ≤ B)
    (hsplit : N ≤ B * (ρ ^ (-M) + ρ ^ d * (L / ρ) ^ q)) :
    N ≤ (2 * B) * ρ ^ (-M) := by
  have ht := tail_factor_le_negative_power hρ hL hgap hq
  calc
    N ≤ B * (ρ ^ (-M) + ρ ^ d * (L / ρ) ^ q) := hsplit
    _ ≤ B * (ρ ^ (-M) + ρ ^ (-M)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl ht) hB
    _ = (2 * B) * ρ ^ (-M) := by ring

/-- `app:ch_osc:rem:osc-difference-frequency` and Section 8: a single positive
scale gap valid even at the smallest separated same-carrier frequency. -/
def separatedCarrierGap : ℝ := 13 / 338

theorem separatedCarrierGap_pos : 0 < separatedCarrierGap := by
  norm_num [separatedCarrierGap]

theorem separatedCarrierGap_lt_one : separatedCarrierGap < 1 := by
  norm_num [separatedCarrierGap]

/-- `app:ch_osc:rem:osc-difference-frequency`: the exact exponent identity for
`L ≤ T^(1+θ)` and `ρ ≥ T^(a-β)` with the paper's fixed exponents. -/
theorem separated_carrier_exponent_identity :
    (carrierExponent - separationExponent) * (1 - separatedCarrierGap) =
      1 + meanSlack := by
  norm_num [carrierExponent, separationExponent, separatedCarrierGap, meanSlack]

/-- `app:ch_osc:eq:osc-source-negative`: the paper scales give the hypothesis
`L ≤ ρ^(1-σ)`, with one fixed `σ=13/338` independent of the requested order. -/
theorem scale_gap_of_separated_carrier {T ρ L : ℝ} (hT : 0 ≤ T)
    (hρ : T ^ (carrierExponent - separationExponent) ≤ ρ)
    (hL : L ≤ T ^ (1 + meanSlack)) :
    L ≤ ρ ^ (1 - separatedCarrierGap) := by
  calc
    L ≤ T ^ (1 + meanSlack) := hL
    _ = (T ^ (carrierExponent - separationExponent)) ^ (1 - separatedCarrierGap) := by
      rw [← Real.rpow_mul hT, separated_carrier_exponent_identity]
    _ ≤ ρ ^ (1 - separatedCarrierGap) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hT _) hρ
        (sub_nonneg.mpr separatedCarrierGap_lt_one.le)

end JanetCartan.Localization
