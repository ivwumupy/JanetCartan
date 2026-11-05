module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.SelectedBoundary
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary.Extraction

/-!
# The selected row's original prescribed source inverse

Project the source inverse returned on the same original selected incidence
row. Keep its `g/rInner/Mlimit/sourceCap` and the complete original continuation:
for each admitted density, first choose its `Vzero`, then for each admitted
source scale choose its `Vop` with the source norm/gap and inverse estimates.
These are not four separate outer hypotheses. The measurement cutoff, source
flow and inner exterior remain those of this row; the history-gap application
must project from this continuation, not select another existential inverse.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

cache_prescribed_source_inverse_boundary
