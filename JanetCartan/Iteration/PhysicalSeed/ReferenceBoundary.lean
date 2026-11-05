module

public import JanetCartan.Iteration.PhysicalSeed.QuotientBoundary
public meta import JanetCartan.Iteration.PhysicalSeed.ReferenceExtraction

/-! Apply arbitrary finite orders, margins and caps to obtain the same H and seed family. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_physical_seed_extension_callback_boundary
cache_physical_seed_seed_boundary
