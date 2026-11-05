module

public import JanetCartan.Analysis.ODE.TimeRescaling.Construction
public import JanetCartan.Analysis.ODE.TimeRescaling.Norms

/-!
# Time rescaling for joint autonomous-flow bounds

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, construct an autonomous flow with one extra
parameter and state coordinate. Transfer the field and section seminorms with
zero derivative loss, then recover space-time seminorms by affine pullback.
The application of the spatial-flow bound belongs to the consuming module.
-/
