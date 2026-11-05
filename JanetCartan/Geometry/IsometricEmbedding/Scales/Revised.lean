module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap

import Mathlib.Tactic

/-!
# The revised manuscript's forcing order and frequency windows

Numerical inputs to `app:prop:ordered-scale-selection` in `paper-v2.tex`.
The existing outer exponents satisfy the revised open windows, but the revised
forcing exponent is different from `JanetCartan.forcingExponent`. These names
are deliberately separate: this file does not change the old sampled-mean
construction or assert that its analytic estimates hold at the revised exponent.

The consumers are `main:eq:all-pair-scales`, the normalized finite-moment target
in `main:lem:smoothing`, and the fixed source order in `main:prop:mean`.
All exponents are fixed before accuracy, chart constants, histories, and targets.
-/

@[expose] public noncomputable section

open Filter

namespace JanetCartan.RevisedScales

/-- `main:eq:A-choice`: the revised baseline order `floor(n/2) + 2`. -/
def baselineOrder (n : ℕ) : ℕ := n / 2 + 2

/-- `main:eq:A-choice`: the fixed Sobolev order of the revised source iteration. -/
def sourceOrder (n : ℕ) : ℕ := 2 * baselineOrder n

/-- `main:eq:A-choice`: the revised forcing exponent, not the old mean exponent. -/
def forcingExponent (n : ℕ) : ℝ := (baselineOrder n : ℝ) + 1 / 2

/-- `main:eq:fixed-outer-exponents` and `main:eq:outer-window`: the existing
outer exponents are a valid choice for the revised manuscript. -/
theorem outer_scale_window :
    0 < samplingSlack ∧ samplingSlack < 1 / 8 ∧
    separationExponent = (1 + samplingSlack) / 3 ∧
    1 < fineExponent ∧ fineExponent < 1 + samplingSlack ∧
    1 + samplingSlack < 1 + separationExponent ∧
    1 + separationExponent < carrierExponent ∧
    carrierExponent < bandExponent ∧ bandExponent < growthExponent ∧
    growthExponent < 3 / 2 ∧
    2 / 3 < coefficientExponent ∧ coefficientExponent < 1 ∧
    coefficientExponent = bandExponent / growthExponent ∧
    0 < cutoffSlack ∧ bandExponent = carrierExponent * (1 + cutoffSlack) := by
  norm_num [samplingSlack, separationExponent, fineExponent, meanSlack,
    carrierExponent, bandExponent, growthExponent, coefficientExponent, cutoffSlack]

/-- `main:eq:all-pair-scales`: choose both strict frequency gaps before any
chart constant, derivative order, or accuracy. -/
theorem strict_frequency_gaps :
    ∃ σ ν : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < ν ∧ ν < 1 ∧
      1 < (1 - σ) * (carrierExponent - separationExponent) ∧
      fineExponent < (1 - ν) * carrierExponent := by
  refine ⟨1 / 100, 1 / 8, ?_⟩
  norm_num [carrierExponent, separationExponent, fineExponent, meanSlack]

/-- `main:eq:preparation-orders`: the concentration exponent is positive and
smaller than the phase-error exponent at the fixed input band. -/
theorem concentration_gap :
    (1 + samplingSlack - fineExponent) / 4 = (3 / 512 : ℝ) ∧
    0 < (1 + samplingSlack - fineExponent) / 4 ∧
    (1 + samplingSlack - fineExponent) / 4 < carrierExponent - fineExponent := by
  norm_num [samplingSlack, fineExponent, meanSlack, carrierExponent]

/-- `main:eq:A-choice`: the revised source order exceeds the dimension and
its forcing gap is exactly one, as used in the normalized target estimate. -/
theorem source_order_and_forcing_gap (n : ℕ) :
    n + 3 ≤ sourceOrder n ∧ n < sourceOrder n ∧
    2 * forcingExponent n - (sourceOrder n : ℝ) = 1 ∧
    separationExponent < 2 * forcingExponent n - (sourceOrder n : ℝ) := by
  have hord : n + 3 ≤ sourceOrder n := by
    dsimp [sourceOrder, baselineOrder]
    omega
  have heq : 2 * forcingExponent n - (sourceOrder n : ℝ) = 1 := by
    simp only [forcingExponent, sourceOrder, Nat.cast_mul, Nat.cast_ofNat]
    ring
  refine ⟨hord, by omega, heq, ?_⟩
  rw [heq]
  norm_num [separationExponent]

/-- `main:eq:all-pair-scales`: one threshold simultaneously absorbs the fixed
constants into the product window, input window, and initial coefficient band,
and makes the smallest product frequency at least two. The gap exponents
precede even these constants. This is a numerical theorem, not a response bound. -/
theorem exists_frequency_window_threshold :
    ∃ σ ν : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < ν ∧ ν < 1 ∧
      ∀ (C Cenv c : ℝ), 0 < C → 0 < c →
        ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin,
          C * R ≤ (R ^ carrierExponent * R ^ (-separationExponent)) ^ (1 - σ) ∧
          C * R ^ fineExponent ≤ (R ^ carrierExponent) ^ (1 - ν) ∧
          Cenv * R ^ coefficientExponent ≤ C * R ^ fineExponent ∧
          2 ≤ c * (R ^ carrierExponent * R ^ (-separationExponent)) := by
  obtain ⟨σ, ν, hσ, hσ₁, hν, hν₁, hpair, hwave⟩ := strict_frequency_gaps
  refine ⟨σ, ν, hσ, hσ₁, hν, hν₁, ?_⟩
  intro C Cenv c hC hc
  have hcoeff : coefficientExponent < fineExponent := by
    norm_num [coefficientExponent, fineExponent, meanSlack]
  have he : 0 < carrierExponent - separationExponent := by
    norm_num [carrierExponent, separationExponent]
  have hlarge : ∀ᶠ R : ℝ in atTop, 2 ≤ R ∧
      C * R ≤ (R ^ carrierExponent * R ^ (-separationExponent)) ^ (1 - σ) ∧
      C * R ^ fineExponent ≤ (R ^ carrierExponent) ^ (1 - ν) ∧
      Cenv * R ^ coefficientExponent ≤ C * R ^ fineExponent ∧
      2 ≤ c * (R ^ carrierExponent * R ^ (-separationExponent)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      eventually_mul_rpow_le_of_exponent_lt C hpair,
      eventually_mul_rpow_le_of_exponent_lt C hwave,
      eventually_mul_rpow_le_of_exponent_lt (Cenv / C) hcoeff,
      eventually_mul_rpow_le_of_exponent_lt (2 / c) he] with R hR hp hw ht hf
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
    have hfreq : R ^ carrierExponent * R ^ (-separationExponent) =
        R ^ (carrierExponent - separationExponent) := by
      rw [← Real.rpow_add hRp]
      rfl
    refine ⟨hR, ?_, ?_, ?_, ?_⟩
    · calc
        C * R ≤ R ^ ((1 - σ) * (carrierExponent - separationExponent)) := by
          simpa only [Real.rpow_one] using hp
        _ = (R ^ carrierExponent * R ^ (-separationExponent)) ^ (1 - σ) := by
          rw [hfreq, ← Real.rpow_mul hRp.le]
          congr 1
          ring
    · calc
        C * R ^ fineExponent ≤ R ^ ((1 - ν) * carrierExponent) := hw
        _ = (R ^ carrierExponent) ^ (1 - ν) := by
          rw [← Real.rpow_mul hRp.le]
          congr 1
          ring
    · calc
        Cenv * R ^ coefficientExponent =
            C * ((Cenv / C) * R ^ coefficientExponent) := by field_simp
        _ ≤ C * R ^ fineExponent := mul_le_mul_of_nonneg_left ht hC.le
    · have hf' : 2 / c ≤ R ^ (carrierExponent - separationExponent) := by
        simpa only [Real.rpow_zero, mul_one] using hf
      rw [hfreq]
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hf'
  obtain ⟨Rmin, hRmin⟩ := eventually_atTop.1 hlarge
  refine ⟨max 2 Rmin, le_max_left _ _, ?_⟩
  intro R hR
  exact (hRmin R ((le_max_right _ _).trans hR)).2

/-- The numerical last step of the normalized target estimate after
`main:lem:smoothing`: `R^(s₀-2A) = R⁻¹ ≤ R^(-β)` for `R ≥ 1`.
The actual Sobolev estimate of the same smoothed target is a separate input. -/
theorem normalized_target_power_le (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    R ^ ((sourceOrder n : ℝ) - 2 * forcingExponent n) = R ^ (-1 : ℝ) ∧
    R ^ ((sourceOrder n : ℝ) - 2 * forcingExponent n) ≤ R ^ (-separationExponent) := by
  have heq := (source_order_and_forcing_gap n).2.2.1
  have hexp : (sourceOrder n : ℝ) - 2 * forcingExponent n = -1 := by linarith
  rw [hexp]
  exact ⟨rfl, Real.rpow_le_rpow_of_exponent_le hR (by norm_num [separationExponent])⟩

/-- `main:eq:A-choice`: the old and revised forcing budgets genuinely differ
already at the endpoint dimension; they cannot be silently substituted. -/
theorem legacy_forcing_exponent_ne_at_five :
    2 * JanetCartan.forcingExponent 5 = (195 / 64 : ℝ) ∧
    2 * forcingExponent 5 = 9 ∧ JanetCartan.forcingExponent 5 ≠ forcingExponent 5 := by
  norm_num [JanetCartan.forcingExponent, meanDerivativeLoss, meanSlack,
    forcingExponent, baselineOrder]

/-- `main:eq:k-cubic` and `main:eq:k-history`: after the actual revised
single step has supplied its fixed losses, one positive integer order satisfies
both strict budgets. Neither loss is identified with its legacy definition. -/
theorem exists_initial_order_for_losses (n rStar : ℕ) (B₀ B₃ : ℝ) :
    ∃ kMin : ℕ, 1 ≤ kMin ∧
      B₃ + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * (kMin : ℝ) ∧
      B₀ + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) := by
  have hgap : 0 < 3 - 2 * growthExponent := by norm_num [growthExponent]
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max 1 (max ((B₃ + 2 * growthExponent + 4) / (3 - 2 * growthExponent))
      (B₀ + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2)))
  have hkone : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have horders := (le_max_right _ _).trans_lt hk
  refine ⟨k, by exact_mod_cast hkone.le, ?_, (le_max_right _ _).trans_lt horders⟩
  have hdiv := (le_max_left _ _).trans_lt horders
  simpa only [mul_comm] using (div_lt_iff₀ hgap).mp hdiv

/-- `new:eq:cubic-gain`: the initial strict order gives the same four-power
reserve at every subsequent order. The true revised cubic loss is a parameter,
so the estimate does not silently substitute the old manuscript's loss. -/
theorem cubic_power_gain_of_initial_order {B₃ R : ℝ} {kMin k : ℕ}
    (horder : B₃ + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * (kMin : ℝ))
    (hk : kMin ≤ k) (hR : 1 ≤ R) :
    R ^ (-3 * (k : ℝ) + B₃) ≤
      R ^ (-2 * growthExponent * ((k : ℝ) + 1)) * R ^ (-4 : ℝ) := by
  have hgap : 0 ≤ 3 - 2 * growthExponent := by norm_num [growthExponent]
  have hkk : (kMin : ℝ) ≤ k := by exact_mod_cast hk
  have hmono := mul_le_mul_of_nonneg_left hkk hgap
  have hexp : -3 * (k : ℝ) + B₃ ≤ -2 * growthExponent * ((k : ℝ) + 1) - 4 := by
    nlinarith only [horder, hmono]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  calc
    _ ≤ R ^ (-2 * growthExponent * ((k : ℝ) + 1) - 4) :=
      Real.rpow_le_rpow_of_exponent_le hR hexp
    _ = _ := by
      rw [← Real.rpow_add hRp]
      congr 1

/-- `main:eq:Q-choice` and `new:eq:cubic-gain`: at `Q = 2k`, the two
separate one-step errors obey the next metric budget with a uniform `2 R⁻⁴`
reserve. This is the arithmetic consequence of a genuine step estimate, not
a construction or an assumed final metric equation. -/
theorem two_error_powers_le_next {B₃ R : ℝ} {kMin k : ℕ}
    (hB₃ : 0 ≤ B₃)
    (horder : B₃ + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * (kMin : ℝ))
    (hk : kMin ≤ k) (hR : 1 ≤ R) :
    R ^ (-(k : ℝ)) * R ^ (-2 * (k : ℝ)) +
        (R ^ (-(k : ℝ))) ^ (3 : ℕ) * R ^ B₃ ≤
      2 * (R ^ (-2 * growthExponent * ((k : ℝ) + 1)) * R ^ (-4 : ℝ)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hfirst : R ^ (-(k : ℝ)) * R ^ (-2 * (k : ℝ)) = R ^ (-3 * (k : ℝ)) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  have hcubic : (R ^ (-(k : ℝ))) ^ (3 : ℕ) * R ^ B₃ = R ^ (-3 * (k : ℝ) + B₃) := by
    rw [← Real.rpow_natCast (R ^ (-(k : ℝ))) 3, ← Real.rpow_mul hRp.le,
      ← Real.rpow_add hRp]
    congr 1
    ring
  rw [hfirst, hcubic]
  have hcompare : R ^ (-3 * (k : ℝ)) ≤ R ^ (-3 * (k : ℝ) + B₃) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  calc
    _ ≤ 2 * R ^ (-3 * (k : ℝ) + B₃) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cubic_power_gain_of_initial_order horder hk hR) (by norm_num)

end JanetCartan.RevisedScales
