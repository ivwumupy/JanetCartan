module

public import JanetCartan.Iteration.PhysicalSeed.OriginalBoundary
public meta import JanetCartan.Iteration.PhysicalSeed.BoundaryExtraction

/-! Apply the arbitrary frame/quotient/direction callback of the one strong initializer. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_physical_seed_quotient_callback_boundary
