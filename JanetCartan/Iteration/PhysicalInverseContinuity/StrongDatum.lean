module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Datum
public import JanetCartan.Iteration.PhysicalDensityContinuity.Strong
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.DatumApplication

/-!
# Actual retained, measured source at fixed contraction

No field difference, smoothness assumption on the current mean, or measured
residual threshold is assumed: these all come from the original data and
the current physical immersion jet. Keep the four original mask conditions,
the original centered measurement, and the literal tangent field. The fixed
reference class and its regularity precede every tolerance and current map.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 28000
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

apply_actual_original_density_to_measured JanetCartan.PhysicalDensityContinuity.StrongDensity.exists_source_density_mean_tolerance
