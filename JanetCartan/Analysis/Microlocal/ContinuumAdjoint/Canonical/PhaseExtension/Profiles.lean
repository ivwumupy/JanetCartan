module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Graph
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Fields

/-!
# Primitive profiles of the canonical affine phase extension

The actual projected-stress transport supplies the global positive graph jets
and all derivative-trade field jets required by
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
The fixed primitive reserve is `2 * (n + 1) + 5`, and both estimates use the
same one high norm `1 + cNorm K (s + 2 * (n + 1) + 5) F`. Constants are chosen
before the varying immersion, and the profiles include `s = 0`.

The field theorem is conditional on the global transverse gap. Its geometric
producer is `jc-adjoint-phase-extension-gap`; the parent retains its actual
instantiation and the final adjoint assembly. No composite graph or field
profile is assumed in either projected theorem.

Source: `app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`.
-/
