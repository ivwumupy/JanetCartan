module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensity
public import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSource
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootQuantitative.Local
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents
public meta import JanetCartan.Iteration.PhysicalBackground.NativeSourceGeometryTemplate

/-!
# Native measurement buffers in the original map and frame ball

Consumer: ResidualProfiles and the exact raw projected-stress transfer for
`app:ch_background:eq:bg-current-profile`. Reuse the existing geometryIndex,
original retained supported chart and its unchanged root center. Even the
six-measurement-radius closed ball lies in the ORIGINAL map/frame ball b.
The similarly named selected conic measurement b is never substituted for it.
Every certificate closes on raw original21 before sigma, history or accuracy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

@[expose] public noncomputable section
open Set Metric
open JanetCartan JanetCartan.ContinuumRow JanetCartan.ActualCarriers
open JanetCartan.ActualCarriers.CurrentFullPhase

realize_native_source_buffers
