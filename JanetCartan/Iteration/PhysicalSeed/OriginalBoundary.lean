module

public import JanetCartan.Iteration.PhysicalSeed.AngularInitializer
public meta import JanetCartan.Iteration.PhysicalSeed.BoundaryExtraction

/-!
# One actual strengthened original seed

All named geometry, domains, rows and continuations project from the ONE
strong initializer. In particular `η_pos` and `generic_leading` come from its
actual retained callback, not from reducing any previously selected weak tuple.
The arbitrary frame/extension/margins/cap/source continuation is retained. Its
same positive extra-cap input now controls both original detector widths before
the one finite incidence selection (`new:sec:order-of-choices`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

cache_physical_seed_common_initializer_boundary
