module

public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarBudgets
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalScalarBoundsApplication

/-!
# Scalar sampling bounds on the actual original physical history

The original selector, source dilation and Schwartz history are unchanged.
A fixed scalar derivative reserve produces numerical map and gap budgets, then
per-row sharp and continuum-mean constants BEFORE the history. The actual
original current-frame producer supplies every scalar low-six phase margin.

`current_bounds` therefore has no current-map norm, metric gap, normal gap,
phase bound, density amplitude, or inverse-response premise. Its remaining
finite-band rate condition is the explicit original frequency admission, not a
successful sample. The SAME common measured/scalar sample must still be chosen
with the actual measured profiles (`app:ch_waves:thm:sampling`,
`new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

open Set Metric
namespace JanetCartan.PhysicalSampling
open PhysicalSeed

namespace OriginalScalarHistory
cache_original_scalar_row_field 0
cache_original_scalar_row_field 1
cache_original_scalar_row_field 2
cache_original_scalar_row_field 3
cache_original_scalar_reached_thresholds
cache_original_scalar_current_inputs
realize_original_scalar_physical_history
end OriginalScalarHistory
end JanetCartan.PhysicalSampling
