module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Constants
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.SourceSum

/-!
# The physical step from the separate original source bounds

This is the finite deduction used to instantiate `main:thm:step` on the
single original construction. It combines the same primary, mean and signed
response, proves the secondary and high input norm internally, and applies
the already checked physical Sobolev step. The four lower error inputs still
belong to their actual producers; this deduction alone is not uniform
existence or Theorem 1.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

open scoped SchwartzMap Matrix.Norms.Frobenius

namespace JanetCartan.RevisedUniform.OriginalStepEstimates

open PhysicalPairs PhysicalPairs.FractionalSize

variable {n N : ℕ}

/-- `main:thm:step`, with the literal secondary and cutoff, all three
individual source norms, and each lower residual's own coefficient. The
finite common coefficient precedes the fields whenever its source costs do;
no estimate of the final increment or of an independently supplied secondary
is an input. -/
theorem increment_estimates_of_source_profiles
    (F : Euclidean n → Euclidean N)
    (P V S : 𝓢(Euclidean n, Euclidean N))
    (g eR H : MetricField n) (D : Set (Euclidean n))
    (CP CV CS : ℕ → ℝ)
    (Csmall Cfast Cstrain Cpair CPL2 CF δ R Q : ℝ)
    (m Qp Qm q kCut : ℕ)
    (hCP : ∀ r, 0 ≤ CP r) (hCV : ∀ r, 0 ≤ CV r) (hCS : ∀ r, 0 ≤ CS r)
    (hCF : 0 ≤ CF) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (hm : 2 * Q < (1 - coefficientExponent) * (m : ℝ))
    (hQp : Q + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (Qp : ℝ))
    (hQm : Q + 2 * RevisedScales.forcingExponent n < (Qm : ℝ))
    (hq : Q + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (q : ℝ))
    (hk : Q + RevisedScales.cubicLoss n < carrierExponent * cutoffSlack * (kCut : ℝ))
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (hsmall : ∀ x ∈ D, ‖(eR - (g - inducedMetric F)) x‖ ≤ Csmall * δ ^ 2)
    (hfast : ∀ x ∈ D, ‖(eR - (g - inducedMetric F)) x‖ ≤
      Cfast * (R ^ coefficientExponent / R) ^ m)
    (hstrain : ∀ x ∈ D, ‖linearizedMetric F P x‖ ≤ Cstrain * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 -
        carrierExponent * (Qp : ℝ)))
    (hmean : ∀ x ∈ D,
      ‖(linearizedMetric F V + H -
        ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹ • eR) x‖ ≤ R ^ (-(Qm : ℝ)))
    (hpair : ∀ x ∈ D,
      ‖linearizedMetric F S x +
        (inducedMetric P - (δ * R ^ RevisedScales.forcingExponent n) ^ 2 • H) x‖ ≤
      Cpair * δ ^ 2 * R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
        (carrierExponent - separationExponent) * (q : ℝ)))
    (hDF : ∀ x ∈ D, ‖fderiv ℝ F x‖ ≤ CF)
    (hP : normAt (RevisedScales.baselineOrder n) P ≤ CP (RevisedScales.baselineOrder n) *
      δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1))
    (hV : ∀ r : ℕ, normAt r V ≤ CV r * R ^ r)
    (hS : ∀ r : ℕ, normAt r S ≤ CS r * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
        (R ^ carrierExponent) ^ (r + 1))
    (hPL2 : PhysicalBernstein.physicalL2Norm P ≤ CPL2 * δ * R ^ RevisedScales.displacementLoss n)
    (hPHigh : normAt (RevisedScales.baselineOrder n + kCut : ℕ) P ≤
      CP (RevisedScales.baselineOrder n + kCut) * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n + kCut : ℕ) : ℝ)) :
    let C := lowerConstant ![Csmall, Cfast, Cstrain, Cpair,
      CP (RevisedScales.baselineOrder n), CV (RevisedScales.baselineOrder n),
      CS (RevisedScales.baselineOrder n), CPL2, CV 0 + CS 0]
    let CH := CP (RevisedScales.baselineOrder n + kCut) +
      CV (RevisedScales.baselineOrder n + kCut) + CS (RevisedScales.baselineOrder n + kCut)
    let K := finalConstant n C CF CH
    let W := physicalSecondary (δ * R ^ RevisedScales.forcingExponent n) V S
    let U := RevisedStage.increment R P W
    PhysicalBernstein.HasFourierSupport (2 * R ^ bandExponent) U ∧
      PhysicalBernstein.physicalL2Norm U ≤ K * δ * R ^ RevisedScales.displacementLoss n ∧
      cNorm D 0 (inducedMetric (F + ⇑U) - g) ≤
        K * (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
  let costs : Fin 9 → ℝ := ![Csmall, Cfast, Cstrain, Cpair,
    CP (RevisedScales.baselineOrder n), CV (RevisedScales.baselineOrder n),
    CS (RevisedScales.baselineOrder n), CPL2, CV 0 + CS 0]
  let C := lowerConstant costs
  let CH := CP (RevisedScales.baselineOrder n + kCut) +
    CV (RevisedScales.baselineOrder n + kCut) + CS (RevisedScales.baselineOrder n + kCut)
  let b := δ * R ^ RevisedScales.forcingExponent n
  let W := physicalSecondary b V S
  have hC : 0 ≤ C := lowerConstant_nonneg costs
  have hC1 : 1 ≤ C := one_le_lowerConstant costs
  have hCH : 0 ≤ CH := add_nonneg (add_nonneg (hCP _) (hCV _)) (hCS _)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hc0 : Csmall ≤ C := cost_le_lowerConstant costs 0
  have hc1 : Cfast ≤ C := cost_le_lowerConstant costs 1
  have hc2 : Cstrain ≤ C := cost_le_lowerConstant costs 2
  have hc3 : Cpair ≤ C := cost_le_lowerConstant costs 3
  have hc4 : CP (RevisedScales.baselineOrder n) ≤ C := cost_le_lowerConstant costs 4
  have hc5 : CV (RevisedScales.baselineOrder n) ≤ C := cost_le_lowerConstant costs 5
  have hc6 : CS (RevisedScales.baselineOrder n) ≤ C := cost_le_lowerConstant costs 6
  have hc7 : CPL2 ≤ C := cost_le_lowerConstant costs 7
  have hc8 : CV 0 + CS 0 ≤ C := cost_le_lowerConstant costs 8
  have hW0 := secondary_l2_of_zero_profiles V S hR (hCV 0) (hV 0) (hS 0)
  have hsum := source_sum_profile (RevisedScales.baselineOrder n + kCut)
    P V S hR (hCV _) (hCS _) hδ.le hδ1 hPHigh (hV _) (hS _)
  have step :
      PhysicalBernstein.HasFourierSupport (2 * R ^ bandExponent) (RevisedStage.increment R P W) ∧
        PhysicalBernstein.physicalL2Norm (RevisedStage.increment R P W) ≤
          2 * RevisedStage.sobolevStageConstant n C * δ * R ^ RevisedScales.displacementLoss n ∧
        cNorm D 0 (inducedMetric (F + ⇑(RevisedStage.increment R P W)) - g) ≤
          RevisedStage.metricErrorConstant n (2 * RevisedStage.sobolevStageConstant n C) CF
            (PhysicalSobolev.embeddingConstant n * CH) *
              (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
    apply RevisedStage.increment_estimates_of_physicalSobolev_profiles
      (e := g - inducedMetric F) (eR := eR) (H := H) (Hself := b ^ 2 • H)
      (Qoff := inducedMetric P - b ^ 2 • H)
      (Emean := linearizedMetric F V + H - (b ^ 2)⁻¹ • eR)
      hC hCF hCH hδ hδ1 hR hQ rfl hm hQp hQm hq hk hF
      (fun _ _ ↦ rfl) rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    · intro x hx
      exact (hsmall x hx).trans (by gcongr)
    · intro x hx
      exact (hfast x hx).trans (by gcongr)
    · intro x hx
      exact (hstrain x hx).trans (by gcongr)
    · intro x hx
      exact (hmean x hx).trans (by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hRpos.le (-(Qm : ℝ)))))
    · intro x hx
      exact (hpair x hx).trans (by gcongr)
    · exact hDF
    · exact hP.trans (by gcongr)
    · have hv : normAt (RevisedScales.baselineOrder n) V ≤
          C * R ^ RevisedScales.baselineOrder n := (hV _).trans (by gcongr)
      simpa only [normAt, Real.rpow_natCast] using hv
    · have hs : normAt (RevisedScales.baselineOrder n) S ≤ C * δ ^ 2 *
          R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
            (R ^ carrierExponent) ^ (RevisedScales.baselineOrder n + 1) :=
        (hS _).trans (by gcongr)
      have he : (RevisedScales.baselineOrder n : ℝ) + 1 =
          ((RevisedScales.baselineOrder n + 1 : ℕ) : ℝ) := by norm_num
      rw [he, Real.rpow_natCast]
      exact hs
    · exact hPL2.trans (by gcongr)
    · exact hW0.trans (by gcongr)
    · simpa only [Nat.cast_add, normAt, CH, physicalSecondary] using hsum
  refine ⟨step.1, step.2.1.trans ?_, step.2.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (l2Cost_le_finalConstant n C CF CH) hδ.le)
      (Real.rpow_nonneg hRpos.le _)
  · exact mul_le_mul_of_nonneg_right (metricCost_le_finalConstant n C CF CH) (by positivity)

end JanetCartan.RevisedUniform.OriginalStepEstimates
end
