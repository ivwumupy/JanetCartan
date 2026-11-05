module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalBoundary
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.Extraction

/-!
# The same initializer's arbitrary quotient callback

For arbitrary positive frame tolerance, supplied ball-extension parameters and
incidence directions, this module applies the original retained callback. The
selected quotient and transport geometry keeps the entire continuation over
arbitrary finite extension orders, positive margins, and user caps. Every
witness comes from `OriginalBoundary.continuation`; there is no second
initializer call and no additional analytic premise.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

cache_prescribed_quotient_callback_boundary
