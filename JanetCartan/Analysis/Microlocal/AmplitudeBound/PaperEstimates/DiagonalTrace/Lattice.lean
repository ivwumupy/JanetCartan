module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.DiagonalTrace.Operator
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.CoefficientDecay

/-!
# The dimension-dependent Sobolev diagonal

For `app:ch_osc:lem:osc-amplitude`, the exact integer order is
`ell = floor(d / 2) + 1`. The previously established summability of
Bessel weights supplies the diagonal constant at this order. All
mode operators are retained from the original Fourier construction.
-/

@[expose] public noncomputable section

open scoped BigOperators ENNReal

namespace JanetCartan.AmplitudeBound.DiagonalTrace

/-- The squared Sobolev coefficient weight at the exact order in
`app:ch_osc:lem:osc-amplitude`. Division of `d` by `2` is natural
division, so the exponent is precisely `floor(d / 2) + 1`. -/
def sobolevWeight (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  (1 + frequencyNorm k ^ 2) ^ (d / 2 + 1)

/-- The original Sobolev coefficient weights are strictly positive. -/
theorem sobolevWeight_pos (d : ℕ) (k : Fin d → ℤ) :
    0 < sobolevWeight d k := by
  unfold sobolevWeight
  positivity

/-- The inverse squared Sobolev weights are summable at the manuscript's
order `floor(d / 2) + 1`; no extra derivative is inserted. -/
theorem summable_inverse_sobolevWeight (d : ℕ) :
    Summable (fun k : Fin d → ℤ ↦ (sobolevWeight d k)⁻¹) := by
  have hdim : (d : ℝ) < 2 * ((d / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : d < 2 * (d / 2 + 1))
  refine (summable_besselWeight hdim).congr ?_
  intro k
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

/-- The fixed dimension-dependent Sobolev diagonal constant in
`app:ch_osc:eq:amplitude-row`. -/
def sobolevDiagonalConstant (d : ℕ) : ℝ :=
  Real.sqrt (∑' k : Fin d → ℤ, (sobolevWeight d k)⁻¹)

/-- Nonnegativity of the Sobolev diagonal constant. -/
theorem sobolevDiagonalConstant_nonneg (d : ℕ) :
    0 ≤ sobolevDiagonalConstant d := Real.sqrt_nonneg _

variable {H H' : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup H'] [NormedSpace ℂ H'] [CompleteSpace H']

/-- The actual lattice Fourier diagonal at the manuscript's minimal
integer Sobolev order. This is the weighted synthesis of the original
mode contractions, with no new operator witness. -/
def sobolevSynthesis (d : ℕ)
    (M : (Fin d → ℤ) → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) :
    lp (fun _ : Fin d → ℤ ↦ H) 2 →L[ℂ] H' :=
  weightedSynthesis (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) M hM

/-- The bounded lattice diagonal has a constant depending only on
dimension, at exactly `ell = floor(d / 2) + 1`. -/
theorem norm_sobolevSynthesis_le (d : ℕ)
    (M : (Fin d → ℤ) → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1) :
    ‖sobolevSynthesis d M hM‖ ≤ sobolevDiagonalConstant d :=
  norm_weightedSynthesis_le (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) M hM

/-- Direct summation of the original lattice Fourier coefficients with
finite `H^ell` energy, as used by the row-amplitude construction. -/
theorem summable_sobolev_mode_series (d : ℕ)
    (M : (Fin d → ℤ) → H →L[ℂ] H') (hM : ∀ k, ‖M k‖ ≤ 1)
    (a : (Fin d → ℤ) → H)
    (ha : Summable (fun k ↦ sobolevWeight d k * ‖a k‖ ^ 2)) :
    Summable (fun k ↦ ‖M k (a k)‖) ∧
      Summable (fun k ↦ M k (a k)) ∧
      ‖∑' k, M k (a k)‖ ≤
        sobolevDiagonalConstant d * Real.sqrt (∑' k, sobolevWeight d k * ‖a k‖ ^ 2) :=
  summable_weighted_mode_series (sobolevWeight d) (sobolevWeight_pos d)
    (summable_inverse_sobolevWeight d) M hM a ha

end JanetCartan.AmplitudeBound.DiagonalTrace
