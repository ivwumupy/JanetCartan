module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.CompactSectionJets
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel

/-!
# Parameter Plancherel estimate for compact carrier tests

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, apply Hilbert-valued parameter
Plancherel to the actual transverse L² section of each compact smooth test.
Its parameter derivatives are controlled by the scalar carrier jets, and
the weight transfers through Fubini and the exact normalization dilation.
This supplies the `hz` input of
`partialUnitaryInverse_test_sobolev_bound_of_split_estimates`, retaining
all three carrier directions and taking no transverse derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

/-- The carrier-frequency part of the compact-test Sobolev estimate in
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. Weighted Fourier membership and
the bound follow from parameter differentiation of the actual compact test
and Hilbert-valued Plancherel, on the literal product Lebesgue measure.
This discharges the `hz` input of
`partialUnitaryInverse_test_sobolev_bound_of_split_estimates`. -/
theorem exists_parameterInitialFourier_test_bound {n : ℕ} (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : carrierInitialTestSpace n,
      MemLp (fun ξ : CarrierVariable n =>
        initialWeight s (ξ.1, (0 : Euclidean (n - 1))) •
        initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
          2 (carrierMeasure n) ∧
      lpNorm (fun ξ : CarrierVariable n =>
        initialWeight s (ξ.1, (0 : Euclidean (n - 1))) •
        initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
          2 (carrierMeasure n) ≤ C * (∑ k ∈ Finset.range (s + 1),
            lpNorm (weightedCarrierJet k 0 f.val) 2 (carrierMeasure n)) := by
  obtain ⟨D, hD, hJ⟩ := exists_carrierTestSlice_jet_bound (n := n) s
  obtain ⟨B, hB, hF⟩ := exists_iteratedParameterFourier_compact_bound (n := n) s
  refine ⟨B * D, mul_nonneg hB hD, fun f => ?_⟩
  obtain ⟨hm, hb⟩ := hF (carrierFubiniEquiv n (carrierInitialTestToLp f))
    (Fubini.slice f.val) (hJ f).1 (hasCompactSupport_carrierTestSlice f)
    (carrierFubiniEquiv_test_eq_slice f)
  obtain ⟨hmem, he⟩ := parameterWeight_initialFourier_partialUnitaryInverse (n := n)
    (fun z => initialWeight s (z, (0 : Euclidean (n - 1))))
    ((measurable_initialWeight s).comp (measurable_id.prodMk measurable_const))
    (carrierInitialTestToLp f) hm
  refine ⟨hmem, he.le.trans (hb.trans ?_)⟩
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hB
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact ((hJ f).2 k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).2

end JanetCartan.ContinuumAdjoint.DensityMultiplier
