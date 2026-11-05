module

public import JanetCartan.Iteration.PhysicalPrimary.LeadingHistory
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.LeadingChart
public meta import JanetCartan.Iteration.PhysicalPrimary.LeadingTemplates

/-!
# One exact current chart and full flow from the physical leading construction

`LeadingData` and `LeadingCell` cache ONE tuple from the actual original
retained leading data proved in `exists_history_retained_leading_data`. Their
`current`, `Φ`, `Y`, and every compatibility/scalar field use the very same
frame, rows and flow witnesses. Consumers must share this tuple; no additional
leading or chart selector is invoked (`main:prop:current-waves`,
`app:ch_background:prop:bg-inverse`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

cache_physical_primary_retained_leading
