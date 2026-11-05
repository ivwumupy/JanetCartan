module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputTests

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Compact smooth frequency tests are dense at raw order zero, where the
shared raw norm is the carrier L² norm (`app:ch_background:eq:bg-density-adjoint`). -/
theorem denseRange_rawTestSobolev_zero :
    DenseRange (rawTestSobolev (n := n) 0) := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, ⟨f, rfl⟩, hlim⟩ := Metric.mem_closure_iff.mp
    (denseRange_carrierInitialTestToLp (n := n) (RawSobolevSpace.toRawL2 0 u))
    (ε := ε) hε
  refine ⟨rawTestSobolev 0 f, ⟨f, rfl⟩, ?_⟩
  rw [dist_eq_norm, RawSobolevSpace.norm_eq]
  change rawSobolevNorm 0 (RawSobolevSpace.toRawL2 0 (u - rawTestSobolev 0 f)) < ε
  rw [map_sub, toRawL2_rawTestSobolev, rawSobolevNorm_zero]
  simpa only [RawSobolevSpace.toRawL2, dist_eq_norm] using hlim

end JanetCartan.ContinuumAdjoint.DensityMultiplier
