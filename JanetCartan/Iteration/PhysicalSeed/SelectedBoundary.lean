module

public import JanetCartan.Iteration.PhysicalSeed.ReferenceBoundary
public meta import JanetCartan.Iteration.PhysicalSeed.BoundaryExtraction
public meta import JanetCartan.Iteration.PhysicalSeed.AngularCache

/-!
Apply the original 21 arguments to the same stronger seed continuation. The
existing positive extra cap bounds both original detector widths. The angular
certificate is appended after every old prefix fact and receives the named
projection `SelectedBoundary.angularWidth_le_aExtra`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_physical_seed_incidence_callback_boundary
cache_physical_seed_angular_width_cap
