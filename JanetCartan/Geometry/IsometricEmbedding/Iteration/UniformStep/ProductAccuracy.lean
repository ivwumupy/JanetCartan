module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledEstimates

/-!
# Signed-product estimates at the fixed stage scales

Convert the complete signed-product bounds of
`ProductSum.complete_signed_product_bounds` to the pair error and secondary
Sobolev budgets of `main:thm:step`. The analytic estimates must hold for one
actual response on the final sampled atoms. Only their scale conversion and
finite internal accuracy selection are proved here.
-/

@[expose] public noncomputable section

namespace JanetCartan.UniformStep

/-- `main:eq:pair-error` at `Q = 2k`: choose the internal product accuracy
before the scale, target and history. Consumed by
`pair_error_after_stage_scaling`; the positive margin uses the original
carrier and separation exponents. -/
theorem exists_pair_accuracy_order (n k q₀ : ℕ) :
    ∃ q : ℕ, q₀ ≤ q ∧
      2 * forcingExponent n + 1 + samplingSlack + 2 * (k : ℝ) ≤
        (carrierExponent - separationExponent) * q := by
  have hgap : 0 < carrierExponent - separationExponent := by
    norm_num [carrierExponent, separationExponent]
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max (q₀ : ℝ) ((2 * forcingExponent n + 1 + samplingSlack + 2 * (k : ℝ)) /
      (carrierExponent - separationExponent)))
  refine ⟨q, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hq).le
  · have h := (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_right _ _) hq)
    simpa only [mul_comm] using h.le

/-- `main:eq:pair-error`: the complete signed-product estimate at its true
frequency `λh` implies the exact pair budget in
`StageConstants.ComponentEstimates.pair`. The actual per-source estimates are
produced by `both-response-transfer`; the sum and its coefficient mass are the
ones in `ProductSum`, with every doubled carrier retained. -/
theorem pair_error_after_stage_scaling {n k q : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {R δ C Ccount Cmass E : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hC : 0 ≤ C) (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hq : 2 * forcingExponent n + 1 + samplingSlack + 2 * (k : ℝ) ≤
      (carrierExponent - separationExponent) * q)
    (herror : E ≤ C * (δ * R ^ forcingExponent n) ^ 2 * ProductSum.coefficientMass μ *
      ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) :
    E ≤ (C * (Ccount * Cmass)) * δ * R ^ (-2 * (k : ℝ)) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmass' := sampled_coefficientMass_le μ hμ hCmass hcount hmass
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hcarrier : ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ =
      R ^ (-((carrierExponent - separationExponent) * (q : ℝ))) := by
    rw [← Real.rpow_add hRpos, ← Real.rpow_natCast, ← Real.rpow_mul hRpos.le,
      ← Real.rpow_neg hRpos.le]
    congr 2
  have hb : (R ^ forcingExponent n) ^ 2 = R ^ (2 * forcingExponent n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]
    congr 1
    norm_num
    ring
  calc
    E ≤ C * (δ * R ^ forcingExponent n) ^ 2 * ProductSum.coefficientMass μ *
        ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ := herror
    _ ≤ C * (δ * R ^ forcingExponent n) ^ 2 *
        ((Ccount * Cmass) * R ^ (1 + samplingSlack)) *
          ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ := by
      gcongr
    _ = (C * (Ccount * Cmass)) * δ ^ 2 *
        R ^ (2 * forcingExponent n + 1 + samplingSlack -
          (carrierExponent - separationExponent) * (q : ℝ)) := by
      rw [mul_pow, hb, hcarrier]
      rw [show 2 * forcingExponent n + 1 + samplingSlack -
          (carrierExponent - separationExponent) * (q : ℝ) =
          (2 * forcingExponent n + (1 + samplingSlack)) +
            (-((carrierExponent - separationExponent) * (q : ℝ))) by ring,
        Real.rpow_add hRpos (2 * forcingExponent n + (1 + samplingSlack))
          (-((carrierExponent - separationExponent) * (q : ℝ))),
        Real.rpow_add hRpos (2 * forcingExponent n) (1 + samplingSlack)]
      ring
    _ ≤ (C * (Ccount * Cmass)) * δ * R ^ (-2 * (k : ℝ)) := by
      gcongr
      linarith

/-- `main:eq:pair-high-size` supplies the secondary profile with the fixed
outside loss `displacementLoss n`. This equality of exponents is independent
of the Sobolev order and accuracy, and preserves the full amplitude `δ²`.
The input is the same response size estimate as in
`ProductSum.complete_signed_product_bounds`. -/
theorem pair_profile_after_stage_scaling {n : ℕ} {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {R δ C Ccount Cmass E : ℝ} (r : ℕ) (hR : 0 < R)
    (hC : 0 ≤ C) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hsize : E ≤ C * (δ * R ^ forcingExponent n) ^ 2 * ProductSum.coefficientMass μ *
      (R ^ carrierExponent) ^ (r + 1)) :
    E ≤ (C * (Ccount * Cmass)) * δ ^ 2 *
      R ^ displacementLoss n * (R ^ carrierExponent) ^ (r : ℝ) := by
  have hmass' := sampled_coefficientMass_le μ hμ hCmass hcount hmass
  have hb : (R ^ forcingExponent n) ^ 2 = R ^ (2 * forcingExponent n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    norm_num
    ring
  calc
    E ≤ C * (δ * R ^ forcingExponent n) ^ 2 * ProductSum.coefficientMass μ *
        (R ^ carrierExponent) ^ (r + 1) := hsize
    _ ≤ C * (δ * R ^ forcingExponent n) ^ 2 *
        ((Ccount * Cmass) * R ^ (1 + samplingSlack)) *
          (R ^ carrierExponent) ^ (r + 1) := by
      gcongr
    _ = _ := by
      rw [mul_pow, hb, pow_succ (R ^ carrierExponent) r,
        ← Real.rpow_natCast (R ^ carrierExponent) r]
      rw [show displacementLoss n =
        (2 * forcingExponent n + (1 + samplingSlack)) + carrierExponent by
          unfold displacementLoss; ring,
        Real.rpow_add hR (2 * forcingExponent n + (1 + samplingSlack)) carrierExponent,
        Real.rpow_add hR (2 * forcingExponent n) (1 + samplingSlack)]
      ring

end JanetCartan.UniformStep
