module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.HighEnvelope.Estimates

/-!
# The high-envelope profile at the complementary scale

The second inequality in the high-envelope display of
`app:ch_response:thm:response-literal-transfer`. The actual producers
`jc-leading-wave` and `jc-current-mean` must supply Euclidean Sobolev
membership and the datum profile. The consumer `jc-response-complement`
must instantiate those inputs; this module does not assert their existence.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Real-order version of the scalar high-envelope calculation in
`app:ch_response:thm:response-literal-transfer`. The fixed scale c is
retained, including when c < 1. -/
theorem highEnvelope_real_scale_bound {ρ K ν c t p : ℝ} (hρ : 1 ≤ ρ)
    (hK : 0 ≤ K) (hν : 0 ≤ ν) (hc : 0 < c) (ht : 0 ≤ t) (htp : t ≤ p)
    (hKρ : K ≤ ρ ^ (1 - ν)) :
    K ^ p * (c * ρ ^ (1 - ν / 2)) ^ (t - p) ≤
      c ^ (t - p) * ρ ^ (t - ν * p / 2) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hKp := Real.rpow_le_rpow hK hKρ (ht.trans htp)
  calc
    _ ≤ (ρ ^ (1 - ν)) ^ p * (c * ρ ^ (1 - ν / 2)) ^ (t - p) :=
      mul_le_mul_of_nonneg_right hKp (by positivity)
    _ = c ^ (t - p) * ρ ^ ((1 - ν / 2) * t - ν * p / 2) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hρpos.le _),
        ← Real.rpow_mul hρpos.le, ← Real.rpow_mul hρpos.le]
      rw [mul_left_comm, ← Real.rpow_add hρpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ (by nlinarith)) (by positivity)

namespace EnvelopeCutoff

/-- The actual high envelope satisfies the paper's profile at
Λ = cρ^(1-ν/2), for `app:ch_response:thm:response-literal-transfer`.
The bounded-frequency case is explicitly included. The datum membership
and profile remain inputs from the wave/current-mean constructions. -/
theorem high_profile_bound {ρ K ν c B R t p C A : ℝ}
    (χ : EnvelopeCutoff d (c * ρ ^ (1 - ν / 2)) B R)
    (hρ : 1 ≤ ρ) (hK : 0 ≤ K) (hν : 0 < ν) (_hν₁ : ν < 1)
    (hc : 0 < c) (ht : 0 ≤ t) (htp : t ≤ p) (hKρ : K ≤ ρ ^ (1 - ν))
    (hC : 0 ≤ C) (hA : 0 ≤ A) {f : L2} (hf : MemFourierSobolev p f)
    (hprofile : fourierSobolevNorm p f ≤ C * A * K ^ p) :
    MemFourierSobolev t (χ.high f) ∧
      fourierSobolevNorm t (χ.high f) ≤
        ((1 + B) * C * c ^ (t - p)) * A * ρ ^ (t - ν * p / 2) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hΛ : 0 < c * ρ ^ (1 - ν / 2) := by positivity
  have hb := χ.bound_nonneg
  have htail : MemFourierSobolev t (χ.high f) ∧
      fourierSobolevNorm t (χ.high f) ≤
        (1 + B) * (c * ρ ^ (1 - ν / 2)) ^ (t - p) * fourierSobolevNorm p f := by
    by_cases hlarge : 1 ≤ c * ρ ^ (1 - ν / 2)
    · exact χ.high_tail_bound hΛ htp hf
    · exact χ.high_bounded_radius_bound hΛ (le_of_not_ge hlarge) htp hf
  refine ⟨htail.1, htail.2.trans ?_⟩
  calc
    _ ≤ (1 + B) * (c * ρ ^ (1 - ν / 2)) ^ (t - p) * (C * A * K ^ p) :=
      mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = ((1 + B) * C * A) * (K ^ p * (c * ρ ^ (1 - ν / 2)) ^ (t - p)) := by ring
    _ ≤ ((1 + B) * C * A) * (c ^ (t - p) * ρ ^ (t - ν * p / 2)) :=
      mul_le_mul_of_nonneg_left
        (highEnvelope_real_scale_bound hρ hK hν.le hc ht htp hKρ) (by positivity)
    _ = _ := by ring

/-- Physical-covector version of the high-envelope estimate in
`app:ch_response:thm:response-literal-transfer`. Its explicit constant uses
c/(2π), since the actual multiplier is χ(2πξ). The input remains Euclidean
Lebesgue data; no torus norm has been substituted. -/
theorem high_physical_profile_bound {ρ K ν c B R t p C A : ℝ}
    (χ : EnvelopeCutoff d (c * ρ ^ (1 - ν / 2)) B R)
    (hρ : 1 ≤ ρ) (hK : 0 ≤ K) (hν : 0 < ν) (_hν₁ : ν < 1)
    (hc : 0 < c) (ht : 0 ≤ t) (htp : t ≤ p) (hKρ : K ≤ ρ ^ (1 - ν))
    (hC : 0 ≤ C) (hA : 0 ≤ A) {f : L2} (hf : MemFourierSobolev p f)
    (hprofile : fourierSobolevNorm p f ≤ C * A * K ^ p) :
    MemFourierSobolev t (χ.physicalCovectorCutoff.high f) ∧
      fourierSobolevNorm t (χ.physicalCovectorCutoff.high f) ≤
        ((1 + B) * C * (c / (2 * Real.pi)) ^ (t - p)) * A * ρ ^ (t - ν * p / 2) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hc' : 0 < c / (2 * Real.pi) := by positivity
  have hΛ : 0 < (c * ρ ^ (1 - ν / 2)) / (2 * Real.pi) := by positivity
  have hb := χ.bound_nonneg
  have htail := χ.physicalCovectorCutoff.high_tail_bound hΛ htp hf
  refine ⟨htail.1, htail.2.trans ?_⟩
  rw [show c * ρ ^ (1 - ν / 2) / (2 * Real.pi) =
    (c / (2 * Real.pi)) * ρ ^ (1 - ν / 2) by ring]
  calc
    _ ≤ (1 + B) * ((c / (2 * Real.pi)) * ρ ^ (1 - ν / 2)) ^ (t - p) *
        (C * A * K ^ p) := mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ = ((1 + B) * C * A) *
        (K ^ p * ((c / (2 * Real.pi)) * ρ ^ (1 - ν / 2)) ^ (t - p)) := by ring
    _ ≤ ((1 + B) * C * A) *
        ((c / (2 * Real.pi)) ^ (t - p) * ρ ^ (t - ν * p / 2)) :=
      mul_le_mul_of_nonneg_left
        (highEnvelope_real_scale_bound hρ hK hν.le hc' ht htp hKρ) (by positivity)
    _ = _ := by ring

end EnvelopeCutoff
end JanetCartan.ResponseTransfer.Complement
