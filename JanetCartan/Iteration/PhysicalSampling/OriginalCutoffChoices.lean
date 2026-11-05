module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCutoffs
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalChoicesApplication

/-!
# The one retained original joint cutoff

`OriginalChoices.Cutoff` names the ONE κ, ψ and cap constructed on the common
original radius and the already-retained mean/comparison radii.
`OriginalChoices.Label` retains the cap for the unchanged original carrier
weight's sharp-band support. Both keep their full admission continuations.
No source, parent, detector, physical radius or external weight is replaced
(`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`).
-/

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalChoices
cache_original_sampling_cutoff_geometry
end JanetCartan.PhysicalSampling.OriginalChoices
