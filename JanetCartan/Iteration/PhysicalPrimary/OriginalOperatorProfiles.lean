module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Iteration.PhysicalGeometry.Retained
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalOperatorProfilesTemplate

/-!
# Native all-order coefficients for the same complete operator

Specialize the actual physical-history coefficient producer to the original
regular family's SAME source-dilated reference and prescribed affine extension.
The full zeroth coefficient is retained. One threshold and the two profiles are
chosen before every history, source frequency and residual word; the compact
measurement set remains arbitrary.

The history regularity cap is at least two greater than the coefficient reserve.
For the complete measured alphabet use coefficient reserve `rCoeff` with
`Rstar + 10 ≤ rCoeff`; thus the actual history cap is at least `Rstar + 12`.
This changes neither the history nor its `kMin`, and selects no new coefficient
admission tolerance.

Consumers: the actual native retarded/solver caches and
`PhysicalEllipticWords.exists_physical_history_measured_residual_hstep`
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_regular:lem:finite-chain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 600000

@[expose] public noncomputable section

retain_original_operator_coefficient_profiles
