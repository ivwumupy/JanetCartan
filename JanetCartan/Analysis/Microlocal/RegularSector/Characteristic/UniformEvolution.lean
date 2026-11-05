module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.AmplitudeBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.ShellGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhaseAgreement
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.FiniteCover
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.PhysicalMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.LocalBounds

/-!
# Signed retarded operators on the retained characteristic construction

The checked deductions here use the literal chart, section and supported
amplitudes of `UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`.
They supply smaller buffered geometry, actual whole-image shell compacts,
original-coefficient phase and amplitude budgets with a single finite low
order, and supported-phase agreement for the solver and residual graphs.
The solver and residual's original retarded test actions and reversed
triangles are preserved by the phase replacement. The actual nested spatial
plateau and dilated right multiplier, finite normalized cover with scale
constant one, all elapsed images of its balls, and physical masks inside the
time plateau are constructed from their fixed geometric carriers.

`exists_retained_local_solver_and_residual` now constructs both bounded
operators from the precise same-witness outputs of
`exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii`.
The retained radius comparisons fit the actual source-compatible slab.
The separate order-three mixed budget chooses the source annulus before
the annular jet budgets, and the enlarged open product contains the entire
closed jet compact. Every primitive graph input is discharged.

The solver uses the literal `W₀+W₁`; the same bounded residual is identified
both with the third collared matrix and with `twoTimePhysicalApply` of the
original correction, including all of `B`. Their supported-phase test
actions, reversed triangles, physical Fourier normalization and positive
and negative integer estimates are retained. One fixed original coefficient
order supplies both low budgets; the high estimates have shifts
`fullLowReserve (d+1)+12` in `Q` and one less in `B`. The local pairing and
restriction-H¹ consumers are connected in `LocalBounds`.

The parent still selects the finite patches and applies the amplitude
producer on each returned angular mask and radial band. This local
same-witness deduction does not assert the unconditional sector theorem.
Sources: `app:ch_regular_base:lem:retarded-kernel`,
`fixed-time-representation`, and `energy-complete-residual` in `paper-v2.tex`.
-/
