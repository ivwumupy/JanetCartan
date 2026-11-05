module

public import JanetCartan.Iteration.PhysicalPairs.FractionalSize

/-!
# The common primary plus secondary at the cutoff order

For `main:eq:joint-physical-profile` and `main:thm:step`, combine the three
original source norms before the final Fourier cutoff. The mean and signed
profiles are used at the same integer order; the secondary is constructed as
`b² V + S`, not supplied with an assumed output estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

open scoped SchwartzMap

namespace JanetCartan.RevisedUniform.OriginalStepEstimates

open PhysicalPairs PhysicalPairs.FractionalSize

variable {n N : ℕ}

/-- The literal `P + (b²V+S)` has the sum of the three original coefficients
and the exact revised displacement exponent. This is the high norm consumed
by `increment_estimates_of_source_profiles`. -/
theorem source_sum_profile (s : ℕ)
    (P V S : 𝓢(Euclidean n, Euclidean N)) {CP CV CS δ R : ℝ}
    (hR : 1 ≤ R) (hCV : 0 ≤ CV) (hCS : 0 ≤ CS)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP : normAt s P ≤ CP * δ * R ^ RevisedScales.displacementLoss n *
      (R ^ carrierExponent) ^ (s : ℝ))
    (hV : normAt s V ≤ CV * R ^ s)
    (hS : normAt s S ≤ CS * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
        (R ^ carrierExponent) ^ (s + 1)) :
    normAt s (P + physicalSecondary (δ * R ^ RevisedScales.forcingExponent n) V S) ≤
      (CP + CV + CS) * δ * R ^ RevisedScales.displacementLoss n *
        (R ^ carrierExponent) ^ (s : ℝ) := by
  have hW := physicalWeightedNorm_secondary_le_revised s V S hR hCV hV hS
  have hquad := RevisedStage.quadratic_amplitude_le hδ hδ1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  calc
    _ ≤ normAt s P +
        normAt s (physicalSecondary (δ * R ^ RevisedScales.forcingExponent n) V S) :=
      RevisedStage.physicalWeightedNorm_add_le _ _ _
    _ ≤ CP * δ * R ^ RevisedScales.displacementLoss n * (R ^ carrierExponent) ^ (s : ℝ) +
        (CV + CS) * δ ^ 2 * R ^ RevisedScales.displacementLoss n *
          (R ^ carrierExponent) ^ s := add_le_add hP hW
    _ ≤ CP * δ * R ^ RevisedScales.displacementLoss n * (R ^ carrierExponent) ^ (s : ℝ) +
        (CV + CS) * δ * R ^ RevisedScales.displacementLoss n *
          (R ^ carrierExponent) ^ s := by
      gcongr
    _ = _ := by rw [Real.rpow_natCast]; ring

/-- Order zero of the same secondary profile is its genuine physical L²
budget, using the existing Plancherel identity. -/
theorem secondary_l2_of_zero_profiles
    (V S : 𝓢(Euclidean n, Euclidean N)) {CV CS δ R : ℝ}
    (hR : 1 ≤ R) (hCV : 0 ≤ CV)
    (hV : normAt (0 : ℕ) V ≤ CV * R ^ (0 : ℕ))
    (hS : normAt (0 : ℕ) S ≤ CS * δ ^ 2 *
      R ^ (2 * RevisedScales.forcingExponent n + 1 + samplingSlack) *
        (R ^ carrierExponent) ^ ((0 : ℕ) + 1)) :
    PhysicalBernstein.physicalL2Norm
      (physicalSecondary (δ * R ^ RevisedScales.forcingExponent n) V S) ≤
        (CV + CS) * δ ^ 2 * R ^ RevisedScales.displacementLoss n := by
  have h := physicalWeightedNorm_secondary_le_revised 0 V S hR hCV hV hS
  simpa only [Nat.cast_zero, physicalWeightedNorm_zero_eq_L2, pow_zero, mul_one] using h

end JanetCartan.RevisedUniform.OriginalStepEstimates
end
