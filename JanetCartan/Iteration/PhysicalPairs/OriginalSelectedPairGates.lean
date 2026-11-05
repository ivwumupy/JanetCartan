module
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistory
public import JanetCartan.Iteration.PhysicalPairs.OriginalSizeSelection
/-! # The unchanged selected history already covers the true pair size reserve

The actual fixed history cap was chosen before all later source, accuracy and
smoothing parameters. Its original moment reserve already pays the stronger
physical pair-size coefficient order. No new cap, width, reference or sigma is
selected (`main:prop:pairs`, `new:sec:order-of-choices`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairGates
/-- The frozen original prehistory meets the physical-size reserve without any
change to its derivative cap or admitted histories (`main:prop:pairs`). -/
theorem history_covers_size (d : ℕ) :
    2 + OriginalSizeSelection.reserve d ≤ RevisedUniform.OriginalSelectedPrehistory.rStar d := by
  have hm := RevisedUniform.OriginalSelectedPrehistory.rStar_ge_moment d
  dsimp only [OriginalSizeSelection.reserve,
    RegularSector.FiniteEvolution.sectorLowOrder,
    RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    FourierIntegral.WholeImageGeometry.wholeImagePhaseReserve,
    FourierIntegral.LowBounds.primitiveNormalReserve]
  simp only [FourierIntegral.FullLowBounds.fullLowReserve_eq]
  omega
end JanetCartan.PhysicalPairs.OriginalSelectedPairGates
#print axioms JanetCartan.PhysicalPairs.OriginalSelectedPairGates.history_covers_size
