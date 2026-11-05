module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The fixed exponents

Definitions from Section 8 and the compatibility assertions of Appendix M.
These choices precede the requested stage accuracy.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- The sampling slack ε. -/
def samplingSlack : ℝ := 1 / 32

/-- The mean-frequency slack θ. -/
def meanSlack : ℝ := 1 / 64

/-- The sample-separation exponent β. -/
def separationExponent : ℝ := 11 / 32

/-- The carrier-frequency exponent a. -/
def carrierExponent : ℝ := 7 / 5

/-- The final Fourier-cutoff slack ζ. -/
def cutoffSlack : ℝ := 1 / 84

/-- The final Fourier-band exponent b_*. -/
def bandExponent : ℝ := 17 / 12

/-- The stage-growth exponent v. -/
def growthExponent : ℝ := 35 / 24

/-- The current-coefficient exponent t. -/
def coefficientExponent : ℝ := 34 / 35

/-- The fine-amplitude exponent s_f. -/
def fineExponent : ℝ := 1 + meanSlack / 2

/-- The mean derivative loss p = (n + 1) / 2. -/
def meanDerivativeLoss (n : ℕ) : ℝ := ((n : ℝ) + 1) / 2

/-- The forcing exponent A. -/
def forcingExponent (n : ℕ) : ℝ := meanDerivativeLoss n * (1 + meanSlack) / 2

/-- The fixed displacement loss B₀ in the finite-stage correction. -/
def displacementLoss (n : ℕ) : ℝ :=
  2 * forcingExponent n + 1 + samplingSlack + carrierExponent

/-- The fixed cubic error loss B₃ in the finite-stage correction. -/
def cubicLoss (n : ℕ) : ℝ :=
  2 * displacementLoss n + 2 * carrierExponent * (meanDerivativeLoss n + 1 / 2)

/-- The outer and fine windows in Section 8. -/
theorem scale_windows :
    separationExponent = (1 + samplingSlack) / 3 ∧
    bandExponent = carrierExponent * (1 + cutoffSlack) ∧
    coefficientExponent = bandExponent / growthExponent ∧
    1 + meanSlack + separationExponent < carrierExponent ∧
    carrierExponent < bandExponent ∧ bandExponent < growthExponent ∧
    growthExponent < 3 / 2 ∧ 0 < coefficientExponent ∧ coefficientExponent < 1 ∧
    1 < fineExponent ∧ fineExponent < 1 + meanSlack ∧
    fineExponent < carrierExponent - separationExponent := by
  norm_num [separationExponent, samplingSlack, bandExponent, carrierExponent,
    cutoffSlack, coefficientExponent, growthExponent, meanSlack, fineExponent]

/-- The positive quadrature margin, including the endpoint n = 5. -/
theorem quadrature_margin {n : ℕ} (hn : 5 ≤ n) :
    3 / 64 ≤ separationExponent * (2 * (n : ℝ) - 1) - 2 * forcingExponent n := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [separationExponent, forcingExponent, meanDerivativeLoss, meanSlack]
  linarith

/-- Equations main:eq:k-cubic and main:eq:k-history admit a fixed integer choice. -/
theorem exists_initial_order (n r : ℕ) :
    ∃ k : ℕ,
      cubicLoss n + 2 * growthExponent + 4 < (3 - 2 * growthExponent) * k ∧
      displacementLoss n + bandExponent * (r + (n : ℝ) / 2) + 2 < k := by
  have hgap : 0 < 3 - 2 * growthExponent := by norm_num [growthExponent]
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max ((cubicLoss n + 2 * growthExponent + 4) / (3 - 2 * growthExponent))
      (displacementLoss n + bandExponent * (r + (n : ℝ) / 2) + 2))
  refine ⟨k, ?_, lt_of_le_of_lt (le_max_right _ _) hk⟩
  have hk' := lt_of_le_of_lt (le_max_left _ _) hk
  simpa only [mul_comm] using (div_lt_iff₀ hgap).mp hk'

end JanetCartan
