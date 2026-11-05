module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.Limit
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.Zero

/-!
# Mixed carrier jets and physical Sobolev Fourier transfer

The Fourier-transfer step in
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`: the compact smooth test estimate
from parameter and transverse Plancherel passes to strong mixed-jet limits in
the existing physical Sobolev space. The constant is uniform over all tests
and limits. The convergence hypotheses are exactly those supplied by
`exists_densitySymbol_weakGraph_bound`; the parent density-multiplier
construction retains their instantiation, the input norm comparison, and
cutoff composition.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Strong limits of compact smooth tests and their mixed carrier jets satisfy
the physical Sobolev estimate in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. The uniform test estimate is proved
by partial Plancherel, and completeness supplies membership of the limit.
All three carrier directions and all `n - 1` initial directions use the shared
product Lebesgue measure and unitary radian normalization.

The density-multiplier assembly consumes this implication with the convergences
from `exists_densitySymbol_weakGraph_bound`. No output Sobolev membership or
norm comparison is assumed. -/
theorem exists_partialUnitaryInverse_sobolev_bound_of_tendsto (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → carrierInitialTestSpace n) (v : CarrierL2 n)
      (J : (k : Fin (s + 1)) →
        Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n)),
      Tendsto (fun j ↦ carrierInitialTestToLp (u j)) atTop (𝓝 v) →
      (∀ k : Fin (s + 1),
        Tendsto (fun j ↦ testWeightedCarrierJet k (s - k) (u j)) atTop (𝓝 (J k))) →
      MemPhysicalSobolev s (partialUnitaryInverse n v) ∧
        physicalSobolevNorm s (partialUnitaryInverse n v) ≤ C * ∑ k, ‖J k‖ := by
  obtain ⟨C, hC, htest⟩ := exists_partialUnitaryInverse_test_sobolev_bound (n := n) s
  exact ⟨C, hC, memPhysicalSobolev_partialUnitaryInverse_of_test_bound s C hC htest⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
