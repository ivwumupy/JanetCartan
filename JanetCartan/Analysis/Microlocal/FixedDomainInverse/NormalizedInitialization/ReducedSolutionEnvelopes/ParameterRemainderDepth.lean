module

public import JanetCartan.Analysis.Operator.FiniteNeumann.Decay

import Mathlib.Tactic.Positivity

/-!
# One common depth for the observed parameter remainder

The actual source jet of order at most `k` costs `ρ^k K^(k+n+1)`.
The same-order observation costs `ρ^(k+2s) K^(k+s)`, and the source and
solver coefficient estimates each cost `L^s`. The original frequency gap
absorbs precisely these factors at one depth chosen before the histories,
parameters, and directions. This is the scalar step connecting
`inverse_remainder_actual_product_source_quadrature` and
`ObservedParameterRemainders` to `parameter_inverse_envelope_of_finite_remainders`
(`app:ch_regular:eq:finite-observation`).
-/

@[expose] public noncomputable section

namespace JanetCartan.FixedDomainInverse

/-- A single finite Neumann depth absorbs the explicit cost of all actual
source-parameter jets through order `k`, at the same spatial order `s`.
The amplitude `A` is arbitrary, so an original derivative reserve or a
tame high/low scalar factor is retained unchanged
(`app:ch_regular:eq:finite-observation`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_observed_parameter_remainder_depth
    {ν : ℝ} (hν : 0 < ν) (n s k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ {ρ L K A C : ℝ},
      1 ≤ ρ → 0 ≤ L → L ≤ K → K ≤ ρ ^ (1 - ν) →
      0 ≤ A → 0 ≤ C →
        C * ρ ^ (k + 2*s) * K ^ (k+s) *
            (A * ρ ^ k * K ^ (k+n+1) * L ^ s * (L/ρ)^N) * L ^ s ≤ C * A := by
  obtain ⟨N, hN, hNe⟩ := exists_finite_neumann_order hν
    ((4*k + 3*s + n + 1 : ℕ) : ℝ) 0 (2*s)
  refine ⟨N, hN, ?_⟩
  intro ρ L K A C hρ hL hLK hwindow hA hC
  have hK : 0 ≤ K := hL.trans hLK
  have hKρ : K ≤ ρ := hwindow.trans
    ((Real.rpow_le_rpow_of_exponent_le hρ (by linarith : 1-ν ≤ (1:ℝ))).trans_eq
      (Real.rpow_one ρ))
  have hKpow : K^(2*k+s+n+1) ≤ ρ^(2*k+s+n+1) :=
    pow_le_pow_left₀ hK hKρ _
  have hscale : ρ^(4*k+3*s+n+1) * L^(2*s) * (L/ρ)^N ≤ 1 := by
    have hs := finite_neumann_scale_bound hρ hL hν.le (hLK.trans hwindow) (2*s) N
      (c := ((4*k+3*s+n+1 : ℕ) : ℝ))
    rw [Real.rpow_natCast] at hs
    refine hs.trans ?_
    exact (Real.rpow_le_rpow_of_exponent_le hρ (by simpa only [neg_zero] using hNe)).trans_eq
      (Real.rpow_zero ρ)
  calc
    _ = C*A * (ρ^(2*k+2*s) * K^(2*k+s+n+1) * L^(2*s) * (L/ρ)^N) := by
      simp only [pow_add, pow_mul]
      ring
    _ ≤ C*A * (ρ^(2*k+2*s) * ρ^(2*k+s+n+1) * L^(2*s) * (L/ρ)^N) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKpow (pow_nonneg (zero_le_one.trans hρ) _))
            (pow_nonneg hL _))
          (pow_nonneg (div_nonneg hL (zero_le_one.trans hρ)) _))
        (mul_nonneg hC hA)
    _ = C*A * (ρ^(4*k+3*s+n+1) * L^(2*s) * (L/ρ)^N) := by
      rw [← pow_add, show 2*k+2*s+(2*k+s+n+1) = 4*k+3*s+n+1 by omega]
    _ ≤ C*A*1 := mul_le_mul_of_nonneg_left hscale (mul_nonneg hC hA)
    _ = _ := mul_one _

end JanetCartan.FixedDomainInverse
