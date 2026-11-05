module

public import JanetCartan.Analysis.Operator.FiniteNeumann.Decay

import Mathlib.Tactic.Positivity

/-!
# The complementary low/high scale calculation

Scalar inputs to `completeComplement_rapidDecay` for the complete-complement
paragraph of `app:ch_response:thm:response-literal-transfer`. The integration
orders are selected before frequency, envelope scales, and datum.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.Complement

/-- Low-envelope scale bound, including a fixed derivative excess `b`, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem lowEnvelope_scale_bound {ρ L ν c d : ℝ} (hρ : 1 ≤ ρ)
    (hL : 0 ≤ L) (hν : 0 ≤ ν) (hc : 0 < c) (hLρ : L ≤ ρ ^ (1 - ν))
    (n b q : ℕ) :
    ρ ^ d * (c * ρ ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) * L ^ b * (L / ρ) ^ q ≤
      c ^ ((n : ℝ) / 2) * ρ ^ (d + (1 - ν / 2) * ((n : ℝ) / 2) + b - ν * q) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hρpos.le _),
    ← Real.rpow_mul hρpos.le]
  calc
    _ = c ^ ((n : ℝ) / 2) *
        (ρ ^ (d + (1 - ν / 2) * ((n : ℝ) / 2)) * L ^ b * (L / ρ) ^ q) := by
      rw [Real.rpow_add hρpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_neumann_scale_bound hρ hL hν hLρ b q) (Real.rpow_nonneg hc.le _)

/-- High-envelope scale bound at `Λ = c ρ^(1-ν/2)` for
`app:ch_response:thm:response-literal-transfer`. The constant `c^(t-p)`
retains the cost of the fixed cutoff scale even when `c < 1`. -/
theorem highEnvelope_scale_bound {ρ K ν c d : ℝ} (hρ : 1 ≤ ρ)
    (hK : 0 ≤ K) (hc : 0 < c) (hKρ : K ≤ ρ ^ (1 - ν)) (t p : ℕ) :
    ρ ^ d * K ^ p * (c * ρ ^ (1 - ν / 2)) ^ ((t : ℝ) - p) ≤
      c ^ ((t : ℝ) - p) * ρ ^ (d + (1 - ν / 2) * t - (ν / 2) * p) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  calc
    _ ≤ ρ ^ d * (ρ ^ (1 - ν)) ^ p *
        (c * ρ ^ (1 - ν / 2)) ^ ((t : ℝ) - p) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hρpos.le _),
        ← Real.rpow_mul hρpos.le, ← Real.rpow_mul_natCast hρpos.le]
      rw [show ρ ^ d * ρ ^ ((1 - ν) * p) *
          (c ^ ((t : ℝ) - p) * ρ ^ ((1 - ν / 2) * ((t : ℝ) - p))) =
          c ^ ((t : ℝ) - p) *
            (ρ ^ d * ρ ^ ((1 - ν) * p) * ρ ^ ((1 - ν / 2) * ((t : ℝ) - p))) by ring,
        ← Real.rpow_add hρpos, ← Real.rpow_add hρpos]
      congr 2
      ring

/-- Select both orders uniformly for the complete complement
(`app:ch_response:thm:response-literal-transfer`). All fixed polynomial losses
are included in `dLow` and `dHigh`; neither may depend on the selected orders. -/
theorem exists_complement_orders {ν : ℝ} (hν : 0 < ν)
    (dLow dHigh Q : ℝ) (n b t : ℕ) :
    ∃ q p : ℕ, 0 < q ∧ 0 < p ∧
      dLow + (1 - ν / 2) * ((n : ℝ) / 2) + b - ν * q ≤ -Q ∧
      dHigh + (1 - ν / 2) * t - (ν / 2) * p ≤ -Q := by
  obtain ⟨q, hq, hqe⟩ := exists_finite_neumann_order hν
    (dLow + (1 - ν / 2) * ((n : ℝ) / 2)) Q b
  obtain ⟨p, hp, hpe⟩ := exists_finite_neumann_order (half_pos hν) dHigh Q t
  refine ⟨q, p, hq, hp, hqe, le_trans ?_ hpe⟩
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

end JanetCartan.ResponseTransfer.Complement
