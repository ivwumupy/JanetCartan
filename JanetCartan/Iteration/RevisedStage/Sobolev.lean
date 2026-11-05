module

public import JanetCartan.Iteration.RevisedStage.SourceProfiles
public import JanetCartan.Analysis.PhysicalSobolev

/-!
# The revised step from actual physical Sobolev source profiles

The consumer is `main:thm:step` in §15 of `paper-v2.tex`. This file discharges
ALL primary/mean/pair derivative estimates and the cutoff derivative tail in
`increment_estimates_of_components`, using the proved physical Sobolev
embedding and the actual cutoff's weighted Fourier tail. No bound on a cutoff
output, derivative, metric error, or Fourier support is a premise.

The remaining inputs belong to the original-data construction: the four lower
metric residuals, the exact common-field identities, and physical Sobolev/L²
profiles of the original Schwartz primary, mean, and pair responses. The
embedding constant is fixed before the fields, history, scale, and accuracy;
only multiplicative constants are enlarged, never the literal revised losses.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap Matrix.Norms.Frobenius

namespace JanetCartan.RevisedStage

open Pseudodifferential PhysicalCutoff

variable {n N : ℕ}

/-- §15 Steps 5--7: one explicit enlargement absorbs both the original lower
error constant and the FIXED physical Sobolev embedding constant. -/
def sobolevStageConstant (n : ℕ) (C : ℝ) : ℝ :=
  (1 + PhysicalSobolev.embeddingConstant n) * C

/-- The constant enlargement in §15 costs no power of the stage frequency. -/
theorem sobolevStageConstant_bounds {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ sobolevStageConstant n C ∧ C ≤ sobolevStageConstant n C ∧
      PhysicalSobolev.embeddingConstant n * C ≤ sobolevStageConstant n C := by
  have hE := PhysicalSobolev.embeddingConstant_nonneg n
  unfold sobolevStageConstant
  exact ⟨by positivity, by nlinarith [mul_nonneg hE hC], by nlinarith⟩

/-- `main:thm:step`: the SAME constructed real Schwartz increment has its
exact band, physical L² bound, and revised two-error metric bound from ORIGINAL
physical Sobolev source norms. In particular there are no `hDP`, `hDV`, `hDS`,
or cutoff-tail hypotheses: all four are discharged by actual analytic theorems.
The residual/profile producers are still explicit; this does not claim the
unconditional original-data construction or uniformity over all histories. -/
theorem increment_estimates_of_physicalSobolev_profiles
    {F : Euclidean n → Euclidean N}
    {P V S W : SchwartzMap (Euclidean n) (Euclidean N)}
    {g e eR H Hself Qoff Emean : MetricField n} {D : Set (Euclidean n)}
    {b C CF CH δ R Q : ℝ} {m Qp Qm q k : ℕ}
    (hC : 0 ≤ C) (hCF : 0 ≤ CF) (hCH : 0 ≤ CH)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (hb : b = δ * R ^ RevisedScales.forcingExponent n)
    (hm : 2 * Q < (1 - coefficientExponent) * (m : ℝ))
    (hQp : Q + RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 <
      carrierExponent * (Qp : ℝ))
    (hQm : Q + 2 * RevisedScales.forcingExponent n < (Qm : ℝ))
    (hq : Q + 2 * RevisedScales.forcingExponent n + 1 + samplingSlack <
      (carrierExponent - separationExponent) * (q : ℝ))
    (hk : Q + RevisedScales.cubicLoss n < carrierExponent * cutoffSlack * (k : ℝ))
    (hF : ∀ x ∈ D, DifferentiableAt ℝ F x)
    (he : Set.EqOn e (g - inducedMetric F) D) (hW : W = b ^ 2 • V + S)
    (hself : Set.EqOn Hself (b ^ 2 • H) D)
    (hoff : Set.EqOn Qoff (inducedMetric P - Hself) D)
    (hmean : Set.EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) D)
    (hsmoothingSmall : ∀ x ∈ D, ‖eR x - e x‖ ≤ C * δ ^ 2)
    (hsmoothingHigh : ∀ x ∈ D, ‖eR x - e x‖ ≤
      C * (R ^ coefficientExponent / R) ^ m)
    (hstrain : ∀ x ∈ D, ‖linearizedMetric F P x‖ ≤ C * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2 -
        carrierExponent * (Qp : ℝ)))
    (hmeanBound : ∀ x ∈ D, ‖Emean x‖ ≤ C * R ^ (-(Qm : ℝ)))
    (hpair : ∀ x ∈ D, ‖linearizedMetric F S x + Qoff x‖ ≤ C * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
        (carrierExponent - separationExponent) * (q : ℝ)))
    (hDF : ∀ x ∈ D, ‖fderiv ℝ F x‖ ≤ CF)
    (hPSob : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight (RevisedScales.baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify P) ξ) 2 volume).toReal ≤ C * δ *
      R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1))
    (hVSob : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight (RevisedScales.baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify V) ξ) 2 volume).toReal ≤ C * R ^ (RevisedScales.baselineOrder n : ℝ))
    (hSSob : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight (RevisedScales.baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify S) ξ) 2 volume).toReal ≤ C * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
      (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + 1))
    (hPL2 : PhysicalBernstein.physicalL2Norm P ≤ C * δ * R ^ RevisedScales.displacementLoss n)
    (hWL2 : PhysicalBernstein.physicalL2Norm W ≤ C * δ ^ 2 * R ^ RevisedScales.displacementLoss n)
    (hHigh : (eLpNorm (fun ξ ↦
      euclideanSobolevWeight ((RevisedScales.baselineOrder n : ℝ) + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify (P + W)) ξ) 2 volume).toReal ≤
      CH * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + k)) :
    PhysicalBernstein.HasFourierSupport (2 * R ^ bandExponent) (increment R P W) ∧
      PhysicalBernstein.physicalL2Norm (increment R P W) ≤
        2 * sobolevStageConstant n C * δ * R ^ RevisedScales.displacementLoss n ∧
      cNorm D 0 (inducedMetric (F + ⇑(increment R P W)) - g) ≤
        metricErrorConstant n (2 * sobolevStageConstant n C) CF
          (PhysicalSobolev.embeddingConstant n * CH) *
          (δ * R ^ (-Q) + δ ^ 3 * R ^ RevisedScales.cubicLoss n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hE := PhysicalSobolev.embeddingConstant_nonneg n
  obtain ⟨hC0, hC1, hEC⟩ := sobolevStageConstant_bounds hC n
  apply increment_estimates_of_components hC0 hCF (mul_nonneg hE hCH)
    hδ hδ1 hR hQ hb hm hQp hQm hq hk hF he hW hself hoff hmean
  · intro x hx
    exact (hsmoothingSmall x hx).trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg δ))
  · intro x hx
    exact (hsmoothingHigh x hx).trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · intro x hx
    exact (hstrain x hx).trans (by gcongr)
  · intro x hx
    exact (hmeanBound x hx).trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · intro x hx
    exact (hpair x hx).trans (by gcongr)
  · exact hDF
  · intro x _
    calc
      _ ≤ PhysicalSobolev.embeddingConstant n * (C * δ *
          R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1)) :=
        (PhysicalSobolev.norm_fderiv_le P x).trans (mul_le_mul_of_nonneg_left hPSob hE)
      _ = (PhysicalSobolev.embeddingConstant n * C) * δ *
          R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) - 1) := by ring
      _ ≤ _ := by gcongr
  · intro x _
    calc
      _ ≤ PhysicalSobolev.embeddingConstant n * (C * R ^ (RevisedScales.baselineOrder n : ℝ)) :=
        (PhysicalSobolev.norm_fderiv_le V x).trans (mul_le_mul_of_nonneg_left hVSob hE)
      _ = (PhysicalSobolev.embeddingConstant n * C) * R ^ (RevisedScales.baselineOrder n : ℝ) := by ring
      _ ≤ _ := by gcongr
  · intro x _
    calc
      _ ≤ PhysicalSobolev.embeddingConstant n * (C * δ ^ 2 *
          R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + 1)) :=
        (PhysicalSobolev.norm_fderiv_le S x).trans (mul_le_mul_of_nonneg_left hSSob hE)
      _ = (PhysicalSobolev.embeddingConstant n * C) * δ ^ 2 *
          R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
          (R ^ carrierExponent) ^ ((RevisedScales.baselineOrder n : ℝ) + 1) := by ring
      _ ≤ _ := by gcongr
  · exact hPL2.trans (by gcongr)
  · exact hWL2.trans (by gcongr)
  · intro x _
    exact PhysicalSobolev.norm_fderiv_truncate_sub_le_of_profile hRp k (P + W) hHigh x

end JanetCartan.RevisedStage
