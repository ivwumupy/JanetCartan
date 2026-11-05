module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap

/-!
# The original pair-scale gap with fixed geometric constants

The source shell uses the true lower frequency `c * lam * h`, while its full
amplitude and phase profiles can contain a fixed constant. The strict original
scale window absorbs both constants at one threshold, before the samples,
target, finite history and requested accuracy. No iteration exponent changes.
-/

@[expose] public noncomputable section

open Filter

namespace JanetCartan.SignedProductEstimates

/-- The original exponents give the pair-scale hypothesis with the fixed
`σ = 1/1000`, including the actual positive geometric frequency constant
and any fixed source-profile constant (`main:eq:all-pair-scales`;
`app:ch_pairs:eq:pairs-lag-envelope`). This threshold precedes all true
frequencies and proof accuracies. -/
theorem exists_signed_pair_scale_threshold {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ R ≥ Rmin, ∀ ρ L : ℝ,
      c * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      L ≤ C * R ^ (1 + meanSlack) →
      2 ≤ ρ ∧ L ≤ ρ ^ (1 - 1 / 1000 : ℝ) := by
  let e : ℝ := carrierExponent - separationExponent
  let s : ℝ := 1 - 1 / 1000
  have he : 0 < e := by norm_num [e, carrierExponent, separationExponent]
  have hs : 0 ≤ s := by norm_num [s]
  have hgap : 1 + meanSlack < e * s := by
    norm_num [e, s, carrierExponent, separationExponent, meanSlack]
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt (2 / c) he)
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt (C / c ^ s) hgap)
  refine ⟨max 2 (max R₁ R₂), le_max_left _ _, ?_⟩
  intro R hR ρ L hρ hL
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hRtwo
  have hRone : R₁ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRtwo' : R₂ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hfreq : R ^ carrierExponent * R ^ (-separationExponent) = R ^ e := by
    rw [← Real.rpow_add hRp]
    rfl
  rw [hfreq] at hρ
  have hlow : 2 / c ≤ R ^ e := by simpa only [Real.rpow_zero, mul_one] using hR₁ R hRone
  have hlow' : 2 ≤ c * R ^ e := by
    have := (div_le_iff₀ hc).mp hlow
    simpa only [mul_comm] using this
  refine ⟨hlow'.trans hρ, ?_⟩
  calc
    L ≤ C * R ^ (1 + meanSlack) := hL
    _ = c ^ s * ((C / c ^ s) * R ^ (1 + meanSlack)) := by
      field_simp
    _ ≤ c ^ s * R ^ (e * s) := mul_le_mul_of_nonneg_left (hR₂ R hRtwo')
      (Real.rpow_nonneg hc.le s)
    _ = (c * R ^ e) ^ s := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hRp.le e), ← Real.rpow_mul hRp.le]
    _ ≤ ρ ^ s := Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg hRp.le e)) hρ hs

end JanetCartan.SignedProductEstimates
