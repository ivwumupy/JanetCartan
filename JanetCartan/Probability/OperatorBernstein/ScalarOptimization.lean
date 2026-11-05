module
public import JanetCartan.Probability.OperatorBernstein.Basic

/-!
# The Bernstein parameter and threshold

The algebraic optimization in Minsker (3.9), used for the threshold
`t² ≥ v + Rt/3` in `app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

namespace JanetCartan.OperatorBernstein

/-- The parameter chosen in Minsker (3.9) (`app:ch_waves:thm:sampling`). -/
def bernsteinParameter (R v t : ℝ) : ℝ := t / (v + R * t / 3)

/-- The positive denominator in the bound of `app:ch_waves:thm:sampling`. -/
theorem bernsteinDenominator_pos {R v t : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 ≤ t) :
    0 < v + R * t / 3 := by positivity

/-- The parameter is positive at positive thresholds (`app:ch_waves:thm:sampling`). -/
theorem bernsteinParameter_pos {R v t : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 < t) :
    0 < bernsteinParameter R v t :=
  div_pos ht (bernsteinDenominator_pos hR hv ht.le)

/-- The parameter satisfies the restriction in Minsker (3.7)
(`app:ch_waves:thm:sampling`). -/
theorem bernsteinParameter_mul_lt_three {R v t : ℝ}
    (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 ≤ t) :
    bernsteinParameter R v t * R < 3 := by
  rw [bernsteinParameter, div_mul_eq_mul_div, div_lt_iff₀ (bernsteinDenominator_pos hR hv ht)]
  nlinarith

/-- The threshold in `app:ch_waves:thm:sampling` gives `θt ≥ 1`. -/
theorem one_le_bernsteinParameter_mul {R v t : ℝ}
    (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 ≤ t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    1 ≤ bernsteinParameter R v t * t := by
  rw [bernsteinParameter, div_mul_eq_mul_div, le_div_iff₀ (bernsteinDenominator_pos hR hv ht)]
  nlinarith

/-- The exponent after the substitution in Minsker (3.9)
(`app:ch_waves:thm:sampling`). -/
theorem bernsteinParameter_exponent {R v t : ℝ}
    (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 ≤ t) :
    (bernsteinParameter R v t) ^ 2 * v /
        (2 * (1 - bernsteinParameter R v t * R / 3)) - bernsteinParameter R v t * t =
      -(t ^ 2) / (2 * (v + R * t / 3)) := by
  have hd := ne_of_gt (bernsteinDenominator_pos hR hv ht)
  unfold bernsteinParameter
  field_simp
  ring

/-- The threshold bounds the one-sided prefactor by seven in Minsker (3.9)
(`app:ch_waves:thm:sampling`). -/
theorem bernsteinParameter_prefactor_le_seven {R v t : ℝ}
    (hR : 0 ≤ R) (hv : 0 < v) (ht : 0 ≤ t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    1 + 6 / (bernsteinParameter R v t * t) ^ 2 ≤ 7 := by
  have h := one_le_bernsteinParameter_mul hR hv ht hthreshold
  have hs : 1 ≤ (bernsteinParameter R v t * t) ^ 2 := by nlinarith
  have hp : 0 < (bernsteinParameter R v t * t) ^ 2 := by linarith
  have : 6 / (bernsteinParameter R v t * t) ^ 2 ≤ 6 := (div_le_iff₀ hp).2 (by linarith)
  linarith
end JanetCartan.OperatorBernstein
