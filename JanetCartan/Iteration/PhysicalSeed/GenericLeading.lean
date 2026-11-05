module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.RetainedCover.Finite
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-!
# Literal arbitrary-map leading continuation

This is the exact budget-before-map callback of the genuine retained finite
selector (`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`). It retains
both ODE systems, their same-row compatibility, and all scalar conclusions.
-/

set_option warningAsError true
set_option maxRecDepth 4000

declare_physical_seed_generic_leading
