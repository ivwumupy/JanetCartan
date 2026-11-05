module

public import JanetCartan.Iteration.PhysicalSeed.PrescribedSource
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.Extraction

/-!
# Retained generic prefix of one strong prescribed common initializer

`OriginalBoundary.initialized` applies the actual stronger prescribed producer,
not an additional hypothesis. Its named `G₀`, geometry, density-product witnesses,
and arbitrary-map `generic_leading` all belong to that one strong choice. The
positive `η` is selected once from its retained `generic_leading_exists` field.
`OriginalBoundary.continuation` retains the complete original arbitrary
`εframe/qext/k` callback, including all finite orders, margins, caps, seed charts,
source inverse, original leading histories and mean continuation.

This is a new choice version of all downstream data, not an identification with
the earlier weak tuple or any independently cached physical tuple. A physical
history caller must choose a positive common frame tolerance below all retained
`η / 28` thresholds before applying the callback and selecting its reference;
generic leading alone does not justify an arbitrary previously chosen tolerance.

The exact proposition aliases keep elaboration local; the generating command
adds only ordinary kernel-checked definitions and theorems. Consumers:
`exists_common_initializer_with_capped_history_inverse` and the actual physical
leading/history construction on these same Mean projections
(`new:sec:order-of-choices`, `app:ch_background:prop:bg-inverse`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

cache_prescribed_common_initializer_boundary
