module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.QuotientBoundary
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary.Extraction

/-!
# The same initializer's arbitrary extension callback and seed

Apply the unchanged callback to arbitrary ball-extension data, finite orders,
positive margins and positive user cap. The selected `θ/H/seed` and the
original incidence, all-cell source, leading-history and mean continuations
all come from that same application. This is an actual producer application,
not a new conditional interface. Prefix aliases change only elaboration cost.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

cache_prescribed_extension_callback_boundary
cache_prescribed_seed_boundary
