module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.WeightSplit
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.TransverseEstimate
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization

/-!
# Assembly of the compact-test partial Fourier estimate

The full initial Sobolev estimate in `app:ch_background:eq:bg-density-adjoint`
follows from parameter differentiation and transverse weighted Plancherel on
actual compact smooth tests. `ParameterEstimate` controls all three carrier
directions, while `TransverseEstimate` controls all `n - 1` initial directions
by η weights. Splitting the full Fourier weight combines these estimates in
the existing physical Sobolev space, with the shared unitary radian normalization
and literal product Lebesgue measure.

The resulting unconditional test estimate supplies the `htest` input of
`memPhysicalSobolev_partialUnitaryInverse_of_test_bound` in `FourierTransfer.Limit`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Assembly of the two restricted Fourier estimates for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. The parameter input is an estimate
by actual `z` derivatives; the transverse input uses only the η-weighted
zeroth carrier jet. The two Plancherel producers are instantiated in
`exists_partialUnitaryInverse_test_sobolev_bound`. -/
theorem partialUnitaryInverse_test_sobolev_bound_of_split_estimates
    (s : ℕ) (C : ℝ) (hC : 0 ≤ C) (f : carrierInitialTestSpace n)
    (hz : MemLp (fun ξ : CarrierVariable n =>
        initialWeight s (ξ.1, (0 : Euclidean (n - 1))) •
          initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ∧
      lpNorm (fun ξ : CarrierVariable n =>
        initialWeight s (ξ.1, (0 : Euclidean (n - 1))) •
          initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ≤ C * (∑ k ∈ Finset.range (s + 1),
          lpNorm (weightedCarrierJet k 0 f.val) 2 (carrierMeasure n)))
    (hη : MemLp (fun ξ : CarrierVariable n =>
        initialWeight s ((0 : CarrierParameter), ξ.2) •
          initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ∧
      lpNorm (fun ξ : CarrierVariable n =>
        initialWeight s ((0 : CarrierParameter), ξ.2) •
          initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ≤
          lpNorm (weightedCarrierJet 0 s f.val) 2 (carrierMeasure n)) :
    MemPhysicalSobolev s (partialUnitaryInverse n (carrierInitialTestToLp f)) ∧
      physicalSobolevNorm s (partialUnitaryInverse n (carrierInitialTestToLp f)) ≤
        ((2 : ℝ) ^ (s - 1) * (C + 1)) * mixedCarrierJetNorm s f.val := by
  obtain ⟨hm, hb⟩ := physicalSobolev_of_split_weight_memLp s _ hz.1 hη.1
  refine ⟨hm, hb.trans ?_⟩
  rw [mul_assoc, add_mul, one_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact hz.2.trans (mul_le_mul_of_nonneg_left
      (sum_unweightedCarrierJet_le_mixedCarrierJetNorm s f) hC)
  · exact hη.2.trans (lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm
      (by omega : 0 + s ≤ s)
      (memLp_weightedCarrierJet_of_compactSupport 0 (s - 0) f.property.1 f.property.2))

/-- Compact smooth tests satisfy the full initial-variable Sobolev estimate
used in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. Parameter differentiation and
Plancherel control the carrier frequencies, and transverse weighted Plancherel
controls the η frequencies, without transverse differentiation.
This supplies the uniform test bound consumed by
`memPhysicalSobolev_partialUnitaryInverse_of_test_bound`. -/
theorem exists_partialUnitaryInverse_test_sobolev_bound (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : carrierInitialTestSpace n,
      MemPhysicalSobolev s (partialUnitaryInverse n (carrierInitialTestToLp f)) ∧
      physicalSobolevNorm s (partialUnitaryInverse n (carrierInitialTestToLp f)) ≤
        C * mixedCarrierJetNorm s f.val := by
  obtain ⟨C, hC, htest⟩ := exists_parameterInitialFourier_test_bound (n := n) s
  refine ⟨(2 : ℝ) ^ (s - 1) * (C + 1), by positivity, fun f => ?_⟩
  exact partialUnitaryInverse_test_sobolev_bound_of_split_estimates s C hC f
    (htest f) (transverseInitialFourier_test_bound s f)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
