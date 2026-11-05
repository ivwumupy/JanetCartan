module

public import JanetCartan.Iteration.PhysicalPairs.Assembly

/-!
# The SAME physical Schwartz secondary W = b²V + S

The original mean14 field V and signed-pair15 field S are combined in physical
Schwartz space BEFORE any final band cutoff. Their original physical-radian
Fourier profiles imply the exact revised secondary budget B₀. In particular
this supplies hWL2 and the secondary half of hHigh to
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
No periodization, additional cutoff, field replacement or altered exponent is
used. Original mean/pair source profiles remain their respective producers'
explicit interfaces, not an assumed secondary output bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory FourierTransform
open scoped SchwartzMap
namespace JanetCartan.PhysicalPairs
open Pseudodifferential PhysicalCutoff

variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "VSpace" => Euclidean N

/-- The literal physical Schwartz secondary from the SAME mean and pair fields
(`main:thm:step`, `main:eq:joint-physical-profile`). -/
def physicalSecondary (b : ℝ) (V S : 𝓢(E, VSpace)) : 𝓢(E, VSpace) := b^2 • V + S

/-- Global secondary identity, not merely agreement on a core or after a lift
(`main:thm:step`). -/
theorem physicalSecondary_coe (b : ℝ) (V S : 𝓢(E, VSpace)) :
    ⇑(physicalSecondary b V S) = b^2 • (V : E → VSpace) + (S : E → VSpace) := rfl

/-- Exact physical-radian Sobolev triangle bound for the SAME secondary. All
weighted L² memberships follow from the actual Schwartz fields. -/
theorem physicalWeightedNorm_secondary_le (s b : ℝ) (V S : 𝓢(E, VSpace)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (physicalSecondary b V S)) ξ) 2 volume).toReal ≤
    b^2 * (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify V) ξ) 2 volume).toReal +
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify S) ξ) 2 volume).toReal := by
  have ht := RevisedStage.physicalWeightedNorm_add_le s (b^2 • V) S
  rw [physicalWeightedNorm_smul, abs_of_nonneg (sq_nonneg b)] at ht
  exact ht

/-- Original mean and complete pair profiles imply the exact revised B₀
physical secondary profile at EVERY integer order, with only the sum of the
two fixed source constants (`main:eq:joint-physical-profile`). -/
theorem physicalWeightedNorm_secondary_le_revised
    (s : ℕ) (V S : 𝓢(E, VSpace)) {δ R CV CS : ℝ}
    (hR : 1 ≤ R) (hCV : 0 ≤ CV)
    (hV : (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify V) ξ) 2 volume).toReal ≤ CV * R^s)
    (hS : (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify S) ξ) 2 volume).toReal ≤
      CS * δ^2 * R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
        (R^carrierExponent)^(s+1)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (physicalSecondary (δ * R^RevisedScales.forcingExponent n) V S)) ξ)
      2 volume).toReal ≤
        (CV+CS) * δ^2 * R^RevisedScales.displacementLoss n * (R^carrierExponent)^s := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hmeanpow : R^(2 * RevisedScales.forcingExponent n) ≤ R^RevisedScales.displacementLoss n := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    unfold RevisedScales.displacementLoss samplingSlack carrierExponent
    linarith
  have hcarrier : R ≤ R^carrierExponent := by
    calc
      R = R^(1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R^carrierExponent := Real.rpow_le_rpow_of_exponent_le hR (by norm_num [carrierExponent])
  have hspow : R^s ≤ (R^carrierExponent)^s := pow_le_pow_left₀ hRp.le hcarrier s
  have hmean : (δ * R^RevisedScales.forcingExponent n)^2 * (CV * R^s) ≤
      CV * δ^2 * R^RevisedScales.displacementLoss n * (R^carrierExponent)^s := by
    calc
      _ = CV * δ^2 * R^(2 * RevisedScales.forcingExponent n) * R^s := by
        rw [mul_pow, ← Real.rpow_mul_natCast hRp.le,
          show RevisedScales.forcingExponent n * (2 : ℕ) =
            2 * RevisedScales.forcingExponent n by norm_num; ring]
        ring
      _ ≤ _ := by gcongr
  have hpair : CS * δ^2 * R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
      (R^carrierExponent)^(s+1) =
      CS * δ^2 * R^RevisedScales.displacementLoss n * (R^carrierExponent)^s := by
    simp only [pow_succ, RevisedScales.displacementLoss, Real.rpow_add hRp]
    ring
  exact ((physicalWeightedNorm_secondary_le s (δ * R^RevisedScales.forcingExponent n) V S).trans
    (add_le_add (mul_le_mul_of_nonneg_left hV (sq_nonneg _)) hS)).trans
      ((add_le_add hmean hpair.le).trans_eq (by ring))

/-- Original order-zero mean and pair profiles give the exact physical L²
secondary budget, for the SAME Schwartz W=b²V+S (`main:eq:step-L2`). -/
theorem physicalL2Norm_secondary_le_revised
    (V S : 𝓢(E, VSpace)) {δ R CV CS : ℝ} (hR : 1 ≤ R) (hCV : 0 ≤ CV)
    (hV : PhysicalBernstein.physicalL2Norm V ≤ CV)
    (hS : PhysicalBernstein.physicalL2Norm S ≤
      CS * δ^2 * R^RevisedScales.displacementLoss n) :
    PhysicalBernstein.physicalL2Norm
      (physicalSecondary (δ * R^RevisedScales.forcingExponent n) V S) ≤
        (CV+CS) * δ^2 * R^RevisedScales.displacementLoss n := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hv : (eLpNorm (fun ξ ↦ euclideanSobolevWeight (0 : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify V) ξ) 2 volume).toReal ≤ CV * R^(0 : ℕ) := by
    simpa only [physicalWeightedNorm_zero_eq_L2, pow_zero, mul_one] using hV
  have hs : (eLpNorm (fun ξ ↦ euclideanSobolevWeight (0 : ℝ) ((2 * Real.pi) • ξ) •
      𝓕 (complexify S) ξ) 2 volume).toReal ≤
      CS * δ^2 * R^(2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
        (R^carrierExponent)^(0+1 : ℕ) := by
    simpa only [physicalWeightedNorm_zero_eq_L2, Nat.zero_add, pow_one,
      RevisedScales.displacementLoss, Real.rpow_add hRp, mul_assoc] using hS
  have hw := physicalWeightedNorm_secondary_le_revised (δ := δ) 0 V S hR hCV
    (by simpa only [Nat.cast_zero] using hv) (by simpa only [Nat.cast_zero] using hs)
  simpa only [Nat.cast_zero, physicalWeightedNorm_zero_eq_L2, pow_zero, mul_one] using hw

end JanetCartan.PhysicalPairs
