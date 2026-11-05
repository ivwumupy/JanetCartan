module

public import JanetCartan.Geometry.IsometricEmbedding.Scales
public import Mathlib.Algebra.Order.Floor.Ring

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite proof orders

The arithmetic of `main:eq:preparation-orders`, `main:eq:Q-choice`, and the proof of
`main:thm:step` in `paper.tex`. A positive carrier exponent and cutoff slack allow
finite natural-number orders to absorb any fixed polynomial loss, uniformly for
`R ≥ 1`. The orders can exceed any previously specified derivative budget.

These are numerical estimates. The error-bound corollaries explicitly assume the
carrier or Fourier-tail estimate supplied by the analytic construction; they do not
construct a Fourier multiplier or prove that analytic estimate.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- Archimedean order selection used in `main:thm:step`: a positive slope eventually
exceeds any fixed loss, while respecting an existing finite order budget. -/
theorem exists_nat_order_mul_gt {a : ℝ} (ha : 0 < a) (L : ℝ) (q₀ : ℕ) :
    ∃ q : ℕ, q₀ ≤ q ∧ L < a * q := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (q₀ : ℝ) (L / a))
  refine ⟨q, Nat.cast_le.mp (le_of_lt ((le_max_left _ _).trans_lt hq)), ?_⟩
  have h := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hq)
  simpa only [mul_comm] using h

/-- The carrier-order comparison in `main:thm:step`, with `λ = R^a`. -/
theorem rpow_carrier_neg_order_le {R a C Q : ℝ} {q : ℕ}
    (hR : 1 ≤ R) (hq : C + Q ≤ a * q) :
    R ^ C * (R ^ a) ^ (-(q : ℝ)) ≤ R ^ (-Q) := by
  rw [← Real.rpow_mul (by linarith : 0 ≤ R),
    ← Real.rpow_add (by linarith : 0 < R)]
  apply Real.rpow_le_rpow_of_exponent_le hR
  nlinarith

/-- Choose a carrier proof order for `main:thm:step`. The same bound holds at
every larger order and every `R ≥ 1`; the chosen order is independent of `R`. -/
theorem exists_carrier_order {a : ℝ} (ha : 0 < a) (C Q : ℝ) (q₀ : ℕ) :
    ∃ q : ℕ, q₀ ≤ q ∧ C + Q < a * q ∧
      ∀ q' : ℕ, q ≤ q' → ∀ R : ℝ, 1 ≤ R →
        R ^ C * (R ^ a) ^ (-(q' : ℝ)) ≤ R ^ (-Q) := by
  obtain ⟨q, hq₀, hq⟩ := exists_nat_order_mul_gt ha (C + Q) q₀
  refine ⟨q, hq₀, hq, ?_⟩
  intro q' hq' R hR
  apply rpow_carrier_neg_order_le hR
  exact hq.le.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hq') ha.le)

/-- Conditional absorption of a carrier error from `main:eq:primary-strain`.
The analytic estimate is the explicit hypothesis `hE`; its prefactor is preserved. -/
theorem carrier_error_le_of_order {E K δ R a C Q : ℝ} {q : ℕ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hq : C + Q ≤ a * q)
    (hE : E ≤ (K * δ) * (R ^ C * (R ^ a) ^ (-(q : ℝ)))) :
    E ≤ K * δ * R ^ (-Q) :=
  hE.trans (mul_le_mul_of_nonneg_left (rpow_carrier_neg_order_le hR hq)
    (mul_nonneg hK hδ))

/-- The numerical Fourier-tail comparison in the proof of `main:thm:step`.
Here `s` can be a Sobolev index or the `C¹` loss `p + 1/2`. -/
theorem rpow_cutoff_tail_le {R a ζ C s Q : ℝ} {k : ℕ}
    (hR : 1 ≤ R) (hk : C + a * s + Q ≤ (a * ζ) * k) :
    R ^ C * (R ^ a) ^ (s - ζ * k) ≤ R ^ (-Q) := by
  rw [← Real.rpow_mul (by linarith : 0 ≤ R),
    ← Real.rpow_add (by linarith : 0 < R)]
  apply Real.rpow_le_rpow_of_exponent_le hR
  nlinarith

/-- Choose a positive Fourier-tail order in `main:thm:step` when `a, ζ > 0`.
It absorbs the fixed loss `C`, uniformly in the scale and in all larger orders. -/
theorem exists_cutoff_order {a ζ : ℝ} (ha : 0 < a) (hζ : 0 < ζ)
    (C s Q : ℝ) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 0 < k ∧ C + a * s + Q < (a * ζ) * k ∧
      ∀ k' : ℕ, k ≤ k' → ∀ R : ℝ, 1 ≤ R →
        R ^ C * (R ^ a) ^ (s - ζ * k') ≤ R ^ (-Q) := by
  obtain ⟨k, hk₀, hk⟩ :=
    exists_nat_order_mul_gt (mul_pos ha hζ) (C + a * s + Q) (max k₀ 1)
  refine ⟨k, (le_max_left _ _).trans hk₀,
    (le_max_right _ _).trans hk₀, hk, ?_⟩
  intro k' hk' R hR
  apply rpow_cutoff_tail_le hR
  exact hk.le.trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk') (mul_pos ha hζ).le)

/-- Conditional absorption of the Fourier tail in `main:thm:step`.
The hypothesis `hE` is the analytic tail estimate; the factor `K * δ` survives. -/
theorem cutoff_error_le_of_order {E K δ R a ζ C s Q : ℝ} {k : ℕ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hk : C + a * s + Q ≤ (a * ζ) * k)
    (hE : E ≤ (K * δ) * (R ^ C * (R ^ a) ^ (s - ζ * k))) :
    E ≤ K * δ * R ^ (-Q) :=
  hE.trans (mul_le_mul_of_nonneg_left (rpow_cutoff_tail_le hR hk)
    (mul_nonneg hK hδ))

/-- The fixed preparation count `J = floor(2A/a)` of `main:eq:preparation-orders`.
For nonnegative `A` and positive `a`, this natural floor equals the integer floor. -/
def preparationOrder (A a : ℝ) : ℕ := ⌊2 * A / a⌋₊

/-- The natural preparation count is the literal integer floor in
`main:eq:preparation-orders` under the manuscript's sign assumptions. -/
theorem preparationOrder_eq_floor {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    (preparationOrder A a : ℤ) = ⌊2 * A / a⌋ := by
  exact Int.natCast_floor_eq_floor (div_nonneg (mul_nonneg (by norm_num) hA) ha.le)

/-- The defining lower bound of the preparation count in `main:eq:preparation-orders`. -/
theorem preparationOrder_mul_le {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    a * preparationOrder A a ≤ 2 * A := by
  have h := Nat.floor_le (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
    ha.le)
  exact (mul_comm _ _).trans_le ((le_div_iff₀ ha).mp h)

/-- The strict preparation inequality `a(J+1) > 2A` in
`main:eq:preparation-orders`; positivity of `a` is essential. -/
theorem lt_preparationOrder_succ_mul {A a : ℝ} (ha : 0 < a) :
    2 * A < a * ((preparationOrder A a : ℝ) + 1) := by
  have h := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (2 * A / a))
  simpa only [preparationOrder, mul_comm] using h

/-- The fixed quadrature order in `main:eq:preparation-orders` and
`app:ch_waves:thm:sampling`; it is chosen before the accuracy. -/
def quadratureOrder (n : ℕ) : ℕ := 2 * n - 1

/-- Real form of the fixed quadrature order from `main:eq:preparation-orders`. -/
theorem quadratureOrder_cast {n : ℕ} (hn : 1 ≤ n) :
    (quadratureOrder n : ℝ) = 2 * (n : ℝ) - 1 := by
  have h : 1 ≤ 2 * n := hn.trans (Nat.le_mul_of_pos_left n (by decide))
  simp only [quadratureOrder, Nat.cast_sub h, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

/-- The paper's fixed quadrature order satisfies `β q_quad > 2A` for `n ≥ 5`
(`main:eq:preparation-orders`), by the already established scale margin. -/
theorem forcingExponent_lt_quadratureOrder_mul {n : ℕ} (hn : 5 ≤ n) :
    2 * forcingExponent n < separationExponent * quadratureOrder n := by
  rw [quadratureOrder_cast (by omega : 1 ≤ n)]
  have h := quadrature_margin hn
  linarith

/-- Both fixed preparation inequalities from `main:eq:preparation-orders`.
The count and quadrature order depend only on the dimension, not on accuracy. -/
theorem preparation_order_inequalities {n : ℕ} (hn : 5 ≤ n) :
    (preparationOrder (forcingExponent n) carrierExponent : ℤ) =
        ⌊2 * forcingExponent n / carrierExponent⌋ ∧
      2 * forcingExponent n <
        carrierExponent * ((preparationOrder (forcingExponent n) carrierExponent : ℝ) + 1) ∧
      2 * forcingExponent n < separationExponent * quadratureOrder n := by
  have ha : 0 < carrierExponent := by norm_num [carrierExponent]
  have hA : 0 ≤ forcingExponent n := by
    dsimp [forcingExponent, meanDerivativeLoss, meanSlack]
    positivity
  exact ⟨preparationOrder_eq_floor hA ha, lt_preparationOrder_succ_mul ha,
    forcingExponent_lt_quadratureOrder_mul hn⟩

/-- Primary strain orders for the fixed scales in `main:thm:step` and
`main:eq:primary-strain`. This also applies to the choice `Q(k) = 2k`
in `main:eq:Q-choice` by substituting that real value for `Q`. -/
theorem exists_primary_strain_order (n : ℕ) (Q : ℝ) (q₀ : ℕ) :
    ∃ q : ℕ, q₀ ≤ q ∧
      forcingExponent n + (1 + samplingSlack) / 2 + Q < carrierExponent * q ∧
      ∀ q' : ℕ, q ≤ q' → ∀ R : ℝ, 1 ≤ R →
        R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ (-(q' : ℝ)) ≤ R ^ (-Q) :=
  exists_carrier_order (by norm_num [carrierExponent])
    (forcingExponent n + (1 + samplingSlack) / 2) Q q₀

/-- The `C¹` Fourier-tail order for the fixed scales in `main:thm:step`.
An additional fixed loss `L` can include the polynomial size of the current field. -/
theorem exists_step_cutoff_order (n : ℕ) (L Q : ℝ) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 0 < k ∧
      displacementLoss n + L + carrierExponent * (meanDerivativeLoss n + 1 / 2) + Q <
        (carrierExponent * cutoffSlack) * k ∧
      ∀ k' : ℕ, k ≤ k' → ∀ R : ℝ, 1 ≤ R →
        R ^ (displacementLoss n + L) *
          (R ^ carrierExponent) ^ (meanDerivativeLoss n + 1 / 2 - cutoffSlack * k') ≤
            R ^ (-Q) :=
  exists_cutoff_order (by norm_num [carrierExponent]) (by norm_num [cutoffSlack])
    (displacementLoss n + L) (meanDerivativeLoss n + 1 / 2) Q k₀

end JanetCartan
