module

public import JanetCartan.Iteration.PhysicalSeed.ReferenceBoundary
public meta import JanetCartan.Iteration.PhysicalSeed.ReferenceExtraction

/-! Select the final G with literal G.map = sourceDilation H.map σ; H remains fixed. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_physical_seed_contracted_reference
