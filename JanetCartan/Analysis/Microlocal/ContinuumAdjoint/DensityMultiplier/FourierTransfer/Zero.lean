module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.GraphClosure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Weights

/-!
# Exact order-zero mixed-jet Fourier transfer

The base case of `app:ch_background:eq:bg-density-adjoint` follows from the
shared partial unitary inverse's Plancherel identity. It requires neither
output membership nor any higher-order norm comparison as a hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The total mixed jet norm at order zero is exactly the carrier L² norm.
This is the base case of the Fourier-transfer estimate in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem mixedCarrierJetNorm_zero (f : carrierInitialTestSpace n) :
    mixedCarrierJetNorm 0 f.val = ‖carrierInitialTestToLp f‖ := by
  simp only [mixedCarrierJetNorm, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
  change (eLpNorm _ 2 (carrierMeasure n)).toReal = _
  change _ = ‖(carrierInitialTest_memLp f).toLp f.val‖
  rw [Lp.norm_toLp]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
    (memLp_weightedCarrierJet_of_compactSupport 0 0 f.property.1 f.property.2).aestronglyMeasurable
    (carrierInitialTest_memLp f).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    simp only [norm_weightedCarrierJet_zero, etaBesselWeight, pow_zero, one_smul])

/-- Partial Plancherel identifies the order-zero test norm with the exact
mixed jet aggregate, with constant one and the shared unitary radian
normalization (`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevNorm_zero_partialUnitaryInverse_test
    (f : carrierInitialTestSpace n) :
    physicalSobolevNorm 0 (partialUnitaryInverse n (carrierInitialTestToLp f)) =
      mixedCarrierJetNorm 0 f.val := by
  rw [physicalSobolevNorm_zero, partialUnitaryInverse_norm, mixedCarrierJetNorm_zero]

/-- The requested strong-limit Fourier transfer at order zero holds with
norm equality. This base case needs no test-estimate hypothesis and retains
the literal product measure (`app:ch_background:eq:bg-density-adjoint`). -/
theorem memPhysicalSobolev_zero_partialUnitaryInverse_of_tendsto
    (u : ℕ → carrierInitialTestSpace n) (v : CarrierL2 n)
    (J : (k : Fin (0 + 1)) →
      Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n))
    (hu : Tendsto (fun j ↦ carrierInitialTestToLp (u j)) atTop (𝓝 v))
    (hJ : ∀ k : Fin (0 + 1),
      Tendsto (fun j ↦ testWeightedCarrierJet k (0 - k) (u j)) atTop (𝓝 (J k))) :
    MemPhysicalSobolev 0 (partialUnitaryInverse n v) ∧
      physicalSobolevNorm 0 (partialUnitaryInverse n v) = ∑ k, ‖J k‖ := by
  refine ⟨memPhysicalSobolev_zero _, ?_⟩
  rw [physicalSobolevNorm_zero, partialUnitaryInverse_norm]
  exact tendsto_nhds_unique hu.norm
    (by simpa only [mixedCarrierJetNorm_zero] using tendsto_mixedCarrierJetNorm 0 u J hJ)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
