module

public import JanetCartan.Iteration.PhysicalSampling.OriginalScalar
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasured
public import JanetCartan.Iteration.PhysicalNormalInverse.TransportOnWorkingRadius
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalChoicesApplication

/-!
# The one retained original candidate geometry

These are the actual geometric witnesses of the scalar, measured corrected,
sharp-band and normal-comparison factories on `originalSamplingRadius`.
Every constant is chosen before reference and source scale. The complete
proved analytic continuation is retained with its witness; in particular the
comparison radii must not be selected independently later.

The original all-cells callback and common cutoff use these named constants.
The later actual primary-profile and one-common-event applications remain
obligations of the producer, not hypotheses counted as a completed sampled row
(`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`).
-/

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalChoices
cache_original_sampling_candidate_geometry
end JanetCartan.PhysicalSampling.OriginalChoices
