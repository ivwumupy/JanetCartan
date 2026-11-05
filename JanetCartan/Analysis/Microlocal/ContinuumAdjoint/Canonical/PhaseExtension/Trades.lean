module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Trades.Fields
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Trades.Canonical

/-!
# Rectangular derivative identities for the canonical phase extension

Global smoothness and a uniform positive transverse gap imply smoothness of
the concrete initial and full-carrier fields and their exact derivative-trade
identities. Neighborhood agreement identifies the extension's spatial matrix
and Gram formula with the actual canonical ones on the complete supported chart.

The actual gap is produced separately by `jc-adjoint-phase-extension-gap`;
its instantiation and the quantitative profiles remain with the parent canonical
construction. These conditional deductions supply the geometric trade inputs to
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/
