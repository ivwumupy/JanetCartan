module

public import JanetCartan.Iteration.PhysicalMean.FixedPicardCoefficientPrecision
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection

/-!
# Original-exponent finite Picard choices with the static coefficient retained

Sampling has exactly the manuscript's ω exponent. The finite contraction
coefficient is NOT assumed ≤1 and is NOT removed from its N-th power.
The same N and proof-tail q are selected before all profile constants; one
threshold then enforces Cρ*R^(-ω)≤1 and the final precision. No physical rate,
window order, source, inverse, sample, or input cutoff is changed.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean

/-- Numerical producer for the original low-linear sampling-plus-transport
coefficient and the finite bilinear contribution. Its consumer is
`sourceResidual_fixedCutoff_middle_le_with_coefficient`. -/
theorem exists_fixedPicard_coefficient_threshold (n : ℕ) (accuracy : ℝ) :
    ∃ N q : ℕ,
      2 * accuracy < ((1 + samplingSlack - fineExponent) / 4) * N ∧
      2 * accuracy < (q : ℝ) * (fineExponent - 1) ∧
      ∀ (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ),
        (∀ s, 0 ≤ Cg s) → (∀ s, 0 ≤ CE s) →
        (∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s) →
      ∀ (b c₀ As At ρ : ℝ), 0 ≤ b → 0 ≤ c₀ → 0 ≤ As → 0 ≤ At →
        ((1 + samplingSlack - fineExponent) / 4) ≤ ρ →
      let D := fun s ↦ ∑ k ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ k s
      let Cρ := As+At+2*c₀*D (n/2+2)
      0 ≤ Cρ ∧ ∃ S : ℝ, 2 ≤ S ∧ ∀ R : ℝ, S ≤ R →
        (As*R^(-((1+samplingSlack-fineExponent)/4))+At*R^(-ρ)) +
          2*c₀*D (n/2+2)*R^(-separationExponent) ≤ Cρ*R^(-((1+samplingSlack-fineExponent)/4)) ∧
        Cρ*R^(-((1+samplingSlack-fineExponent)/4)) ≤ 1 ∧
        (2*fourierInterpolationConstant n 1 (n/2+2)*
          finiteSourceResidualConstantWithCoefficient Cg CE CQ b Cρ (n/2+2) q N)*
          R^(-separationExponent)*
          Real.sqrt (R^(-((1+samplingSlack-fineExponent)/4)*(N : ℝ))+
            (R/R^fineExponent)^q) ≤ R^(-accuracy) := by
  obtain ⟨N,q,hN,hq,hprecision⟩ := exists_source_iteration_precision accuracy
  refine ⟨N,q,hN,hq,?_⟩
  intro Cg CE CQ hCg hCE hCQ b c₀ As At ρ hb hc₀ hAs hAt hρ D Cρ
  let ω := (1+samplingSlack-fineExponent)/4
  have hω : 0 < ω := RevisedScales.concentration_gap.2.1
  have hβ : ω < separationExponent := (source_iteration_fixed_gaps n).2.2.1
  have hD (s : ℕ) : 0 ≤ D s := Finset.sum_nonneg fun k _ ↦
    sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ k s
  have hcD : 0 ≤ 2*c₀*D (n/2+2) := mul_nonneg (mul_nonneg (by norm_num) hc₀) (hD _)
  have hCρ : 0 ≤ Cρ := add_nonneg (add_nonneg hAs hAt) hcD
  refine ⟨hCρ,?_⟩
  have hlarge := eventually_mul_rpow_le_of_exponent_lt Cρ (show -ω < (0 : ℝ) by linarith)
  obtain ⟨S₀,hS₀⟩ := Filter.eventually_atTop.mp hlarge
  have hC : 0 ≤ 2*fourierInterpolationConstant n 1 (n/2+2)*
      finiteSourceResidualConstantWithCoefficient Cg CE CQ b Cρ (n/2+2) q N :=
    mul_nonneg (mul_nonneg (by norm_num) (fourierInterpolationConstant_nonneg _ _ _))
      (finiteSourceResidualConstantWithCoefficient_nonneg Cg CE CQ hCg hCE hCQ hb hCρ _ _ _)
  obtain ⟨S₁,hS₁,hfinal⟩ := hprecision _ hC
  refine ⟨max S₀ S₁,hS₁.trans (le_max_right _ _),?_⟩
  intro R hR
  have hRone : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 2).trans
    (hS₁.trans ((le_max_right _ _).trans hR))
  have ht : At*R^(-ρ) ≤ At*R^(-ω) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hRone (by dsimp only [ω]; linarith)) hAt
  have hqterm : (2*c₀*D (n/2+2))*R^(-separationExponent) ≤
      (2*c₀*D (n/2+2))*R^(-ω) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hRone (by linarith)) hcD
  refine ⟨?_,?_,hfinal R ((le_max_right _ _).trans hR)⟩
  · calc
      _ ≤ As*R^(-ω)+At*R^(-ω)+(2*c₀*D (n/2+2))*R^(-ω) :=
        add_le_add (add_le_add le_rfl ht) hqterm
      _ = _ := by dsimp only [Cρ]; ring
  · simpa only [Real.rpow_zero] using hS₀ R ((le_max_left _ _).trans hR)

end JanetCartan.PhysicalMean
end
