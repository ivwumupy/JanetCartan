module

public import JanetCartan.Iteration.PhysicalPairs.Realization
public import JanetCartan.Iteration.RevisedStage.SourceProfiles

/-!
# Full signed assembly in physical Fourier norm

This is the finite assembly part of paper-v2 `main:prop:pairs`. Its lower
individual estimates are produced by the same ambient reconstruction applied
to the actual normalized inverse and complete signed-source profiles. The
operator, physical norm, and field are never changed during finite summation.
This deduction does not itself instantiate that original-data construction.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalPairs

open Pseudodifferential PhysicalCutoff

variable {n N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => Euclidean n
local notation "V" => Euclidean N
local notation "C" => EuclideanSpace ℂ (Fin N)

private def weightedFourierToLp (s : ℝ) :
    𝓢(E, V) →L[ℝ] Lp C 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℝ C 2 volume).comp
    ((SchwartzMap.smulLeftCLM C
      (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ))).comp
      ((fourierCLM ℝ 𝓢(E, C)).comp (SchwartzMap.postcompCLM euclideanComplexInclusion)))

private theorem norm_weightedFourierToLp (s : ℝ) (u : 𝓢(E, V)) :
    ‖weightedFourierToLp s u‖ =
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  change ‖(SchwartzMap.smulLeftCLM C
    (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ))
    (𝓕 (complexify u))).toLp 2 volume‖ = _
  rw [SchwartzMap.norm_toLp]
  congr 2
  exact SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_physicalWeight s) _

/-- Exact scalar homogeneity of the original physical radian Fourier norm.
This is used for b²V in the SAME secondary W=b²V+S; finiteness is supplied by
Schwartz regularity (`main:eq:joint-physical-profile`, `main:thm:step`). -/
theorem physicalWeightedNorm_smul (s b : ℝ) (u : 𝓢(E, V)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (b • u)) ξ) 2 volume).toReal =
      |b| * (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
  rw [← norm_weightedFourierToLp, ← norm_weightedFourierToLp, map_smul, norm_smul, Real.norm_eq_abs]

/-- Actual physical signed assembly retains all doubled plus carriers and
excludes only the minus diagonal (`main:prop:pairs`). This is a deduction from
individual SAME-field physical profiles, not an assumed full correction bound. -/
theorem physicalWeightedNorm_signedSum_le
    (s : ℝ) (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (plus minus : ι → ι → 𝓢(E, V)) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i j, (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (plus i j)) ξ) 2 volume).toReal ≤ B)
    (hm : ∀ i j, j ≠ i → (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (minus i j)) ξ) 2 volume).toReal ≤ B) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (-ProductSum.weightedSignedSum b μ plus minus)) ξ)
      2 volume).toReal ≤ 2 * B * b^2 * ProductSum.coefficientMass μ := by
  rw [← norm_weightedFourierToLp, map_neg, norm_neg]
  exact ProductSum.norm_map_weightedSignedSum_le (weightedFourierToLp s).toLinearMap
    b μ hμ plus minus hB
    (fun i j ↦ by simpa only [ContinuousLinearMap.coe_coe, norm_weightedFourierToLp] using hp i j)
    (fun i j hij ↦ by simpa only [ContinuousLinearMap.coe_coe, norm_weightedFourierToLp] using hm i j hij)

/-- The exact v2 sample-count scaling of the SAME complete signed correction.
The forcing exponent is the revised `A`, not the old manuscript exponent
(`main:prop:pairs`). No separation loss appears in the physical size estimate. -/
theorem physicalWeightedNorm_signedSum_le_revised
    (r : ℕ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (plus minus : ι → ι → 𝓢(E, V)) {B Ccount Cmass δ R : ℝ}
    (hB : 0 ≤ B) (hCmass : 0 ≤ Cmass) (hR : 0 < R)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R^(1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hp : ∀ i j, (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
      𝓕 (complexify (plus i j)) ξ) 2 volume).toReal ≤ B * (R^carrierExponent)^(r+1))
    (hm : ∀ i j, j ≠ i → (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
      𝓕 (complexify (minus i j)) ξ) 2 volume).toReal ≤ B * (R^carrierExponent)^(r+1)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
      𝓕 (complexify (-ProductSum.weightedSignedSum
        (δ * R^RevisedScales.forcingExponent n) μ plus minus)) ξ)
      2 volume).toReal ≤
      (2 * B * Ccount * Cmass) * δ^2 *
        R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
          (R^carrierExponent)^(r+1) := by
  have hbase := physicalWeightedNorm_signedSum_le (r : ℝ)
    (δ * R^RevisedScales.forcingExponent n) μ hμ plus minus
    (mul_nonneg hB (by positivity)) hp hm
  have hcoeff := (ProductSum.coefficientMass_le_card_mul μ hμ hmass).trans
    (mul_le_mul_of_nonneg_right hcount hCmass)
  apply hbase.trans
  calc
    _ ≤ 2 * (B * (R^carrierExponent)^(r+1)) *
        (δ * R^RevisedScales.forcingExponent n)^2 *
          (Ccount * R^(1 + samplingSlack) * Cmass) := by gcongr
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (R^RevisedScales.forcingExponent n) 2,
        ← Real.rpow_mul hR.le]
      rw [show 2 * RevisedScales.forcingExponent n + 1 + samplingSlack =
        RevisedScales.forcingExponent n * 2 + (1 + samplingSlack) by ring]
      simp only [Real.rpow_add hR]
      ring_nf

omit [DecidableEq ι] in
/-- Exact v2 finite signed residual scaling, preserving the full `δ²` and the
true carrier/separation exponent. The input is the finite signed error obtained
from individual sources through the SAME response, not the desired full pair
budget (`main:prop:pairs`). No old forcing exponent is used. -/
theorem signedResidual_le_revised_count_mass
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {R δ Cerror Ccount Cmass e : ℝ} (hR : 0 < R) (hC : 0 ≤ Cerror) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R^(1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass) (q : ℕ)
    (herror : e ≤ Cerror * (δ * R^RevisedScales.forcingExponent n)^2 *
      ProductSum.coefficientMass μ * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) :
    e ≤ (Cerror * Ccount * Cmass) * δ^2 *
      R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
        (carrierExponent - separationExponent) * (q : ℝ)) := by
  have hcoeff := (ProductSum.coefficientMass_le_card_mul μ hμ hmass).trans
    (mul_le_mul_of_nonneg_right hcount hCmass)
  have hcarrier : ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ =
      R^(-((carrierExponent - separationExponent) * (q : ℝ))) := by
    rw [← Real.rpow_add hR, ← Real.rpow_natCast, ← Real.rpow_mul hR.le,
      ← Real.rpow_neg hR.le]
    congr 2
  apply herror.trans
  calc
    _ ≤ Cerror * (δ * R^RevisedScales.forcingExponent n)^2 *
        (Ccount * R^(1 + samplingSlack) * Cmass) *
          ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ := by gcongr
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (R^RevisedScales.forcingExponent n) 2,
        ← Real.rpow_mul hR.le, hcarrier]
      rw [show 2 * RevisedScales.forcingExponent n + 1 + samplingSlack -
        (carrierExponent - separationExponent) * (q : ℝ) =
        RevisedScales.forcingExponent n * 2 + (1 + samplingSlack) +
          (-((carrierExponent - separationExponent) * (q : ℝ))) by ring]
      simp only [Real.rpow_add hR]
      ring_nf

/-- Zeroth physical weighted Fourier norm is exactly physical L² of the SAME
real Schwartz field, giving the pair L² clause from its order-zero size
(`main:prop:pairs`, `main:eq:final-Cr`). -/
theorem physicalWeightedNorm_zero_eq_L2 (u : 𝓢(E, V)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight 0 ((2 * Real.pi) • ξ) •
      𝓕 (complexify u) ξ) 2 volume).toReal = PhysicalBernstein.physicalL2Norm u := by
  simp only [euclideanSobolevWeight_zero, one_smul]
  rw [← SchwartzMap.norm_toLp, SchwartzMap.norm_fourier_toL2_eq,
    norm_complexify_toLp, PhysicalBernstein.physicalL2Norm_eq_norm_toLp]

end JanetCartan.PhysicalPairs
