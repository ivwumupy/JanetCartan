module

public import JanetCartan.Iteration.PhysicalSeed.SelectedBoundary
public meta import JanetCartan.Iteration.PhysicalSeed.ReferenceExtraction

/-! Project the actual prescribed source inverse on the same newly strengthened tuple. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_physical_seed_source_inverse_boundary
