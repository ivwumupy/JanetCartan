module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalAngularSourceCallback
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.Extraction

/-!
# The same prescribed initializer's incidence selection

For arbitrary incidence radius and positive extra-cap function, apply the
stronger late callback derived on the ALREADY chosen original Mean H and seed.
Choose one NEW row/source version retaining both spatial and angular user caps
and the complete old raw/source/inverse/exterior/comparison continuation. The
user cap may be intersected with the original raw cap before this one selection.
No equality with an earlier weak selected row/source is asserted; H and seed
are not reselected here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

cache_prescribed_incidence_callback_boundary

namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.SelectedBoundary

/-- The same selected detector satisfies the prescribed angular cap for the
original scalar sampling construction (`new:eq:amplitude-test`). -/
public alias angularWidth_le_aExtra := fact105

end JanetCartan.ContinuumInverse.InitializedCappedHistory.SelectedBoundary
