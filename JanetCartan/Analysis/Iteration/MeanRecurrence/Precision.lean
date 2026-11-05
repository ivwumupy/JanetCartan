module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # The finite precision count in `main:lem:mean-recurrence` of paper.tex -/

@[expose] public noncomputable section

namespace JanetCartan.MeanRecurrence

/-- `main:lem:mean-recurrence`: the prescribed count `⌊Q / γ⌋ + 1`. -/
def precisionSteps (Q γ : ℝ) : ℕ := ⌊Q / γ⌋₊ + 1

/-- `main:lem:mean-recurrence`: the prescribed count exceeds the required
precision divided by the contraction exponent. -/
theorem lt_precisionSteps_mul {Q γ : ℝ} (hγ : 0 < γ) :
    Q < γ * (precisionSteps Q γ : ℝ) := by
  have h := (div_lt_iff₀ hγ).mp (Nat.lt_floor_add_one (Q / γ))
  simpa only [precisionSteps, Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- `main:lem:mean-recurrence`: `I = ⌊Q / γ⌋ + 1` geometric steps with
ratio `H^(-γ)` reach the requested `H^(-Q)` relative accuracy. -/
theorem geometric_precision_of_count {H Q γ : ℝ} (hH : 1 ≤ H) (hγ : 0 < γ) :
    (H ^ (-γ)) ^ precisionSteps Q γ ≤ H ^ (-Q) := by
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ H)]
  apply Real.rpow_le_rpow_of_exponent_le hH
  have h := lt_precisionSteps_mul (Q := Q) hγ
  nlinarith

end JanetCartan.MeanRecurrence
