module

public import JanetCartan.Analysis.Iteration.BandHistory.Geometric
public import JanetCartan.Geometry.IsometricEmbedding.Scales

import Mathlib.Tactic.Ring

/-!
# The current coefficient scale and its strict power gap

The numerical part of `main:prop:current-scale`. The scale and the positive gap
are fixed before choosing derivative orders or accuracies. No coefficient
estimate or response construction is asserted in this module.
-/

@[expose] public noncomputable section

open Filter Topology

namespace JanetCartan

/-- `main:prop:current-scale`: the paper's `T_j = R_j^t`. -/
def currentCoefficientScale (R : ℝ) (j : ℕ) : ℝ :=
  historyScale R growthExponent j ^ coefficientExponent

/-- `main:lem:history`: every stage scale is at least the initial scale. -/
theorem le_historyScale {R : ℝ} (hR : 1 ≤ R) (j : ℕ) :
    R ≤ historyScale R growthExponent j := by
  exact Real.self_le_rpow_of_one_le hR
    (one_le_pow₀ (by norm_num [growthExponent]))

/-- `main:prop:current-scale`: the current scale is at least one at every stage. -/
theorem one_le_currentCoefficientScale {R : ℝ} (hR : 1 ≤ R) (j : ℕ) :
    1 ≤ currentCoefficientScale R j :=
  Real.one_le_rpow (hR.trans (le_historyScale hR j))
    (by norm_num [coefficientExponent])

/-- `main:lem:history`: the previous stage's Fourier band is exactly the current
coefficient scale, without a stage-dependent factor. -/
theorem currentCoefficientScale_succ {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    currentCoefficientScale R (j + 1) =
      historyScale R growthExponent j ^ bandExponent := by
  simp only [currentCoefficientScale, historyScale, ← Real.rpow_mul hR, pow_succ]
  congr 1
  have h : growthExponent * coefficientExponent = bandExponent := by
    norm_num [growthExponent, coefficientExponent, bandExponent]
  rw [mul_assoc, h]

/-- `main:prop:current-scale`, `main:eq:all-pair-scales`: the stated fixed
choice `σ = 1/1000` leaves strict room for both coefficient and fine scales. -/
theorem current_coefficient_exponent_gaps :
    coefficientExponent < 1 ∧
    coefficientExponent < (carrierExponent - separationExponent) * (1 - 1 / 1000) ∧
    fineExponent < (carrierExponent - separationExponent) * (1 - 1 / 1000) := by
  norm_num [coefficientExponent, carrierExponent, separationExponent, fineExponent, meanSlack]

/-- `main:prop:current-scale`: a strict power gap absorbs any fixed chart constant. -/
theorem eventually_mul_rpow_le_of_exponent_lt (C : ℝ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ R : ℝ in atTop, C * R ^ p ≤ R ^ q := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually
    (eventually_ge_atTop C)
  filter_upwards [hg, eventually_gt_atTop (0 : ℝ)] with R hC hR
  calc
    C * R ^ p ≤ R ^ (q - p) * R ^ p :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hR.le _)
    _ = R ^ q := by rw [← Real.rpow_add hR]; congr 1; ring

/-- `main:prop:current-scale`: one initial-scale threshold works for all stages,
absorbing any fixed chart constant into `(λ_j h_j)^(1-σ)`, with `σ=1/1000`.
The threshold has no derivative-order or accuracy parameter. -/
theorem exists_current_coefficient_scale_gap (C : ℝ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin, ∀ j : ℕ,
      C * currentCoefficientScale R j ≤
        (historyScale R growthExponent j ^ carrierExponent *
          historyScale R growthExponent j ^ (-separationExponent)) ^ (1 - 1 / 1000 : ℝ) := by
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt C current_coefficient_exponent_gaps.2.1)
  refine ⟨max 2 S, le_max_left _ _, ?_⟩
  intro R hR j
  have hRone : 1 ≤ R := le_trans (by norm_num) ((le_max_left _ _).trans hR)
  have hstage : R ≤ historyScale R growthExponent j := le_historyScale hRone j
  have hpos : 0 < historyScale R growthExponent j :=
    lt_of_lt_of_le zero_lt_one (hRone.trans hstage)
  have hlarge : S ≤ historyScale R growthExponent j :=
    ((le_max_right _ _).trans hR).trans hstage
  simpa only [currentCoefficientScale, ← Real.rpow_add hpos,
    ← Real.rpow_mul hpos.le, ← sub_eq_add_neg] using hS _ hlarge

end JanetCartan
