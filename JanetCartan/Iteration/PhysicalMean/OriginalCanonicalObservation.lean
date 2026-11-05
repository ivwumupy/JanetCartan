module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# The unchanged original observation cutoff

The fixed source cutoff is used only to extend the original derivative to the
auxiliary torus. Its genuine one-germ contains the entire measurement support;
no physical wave or source is recut (`app:ch_mean_pairs:defn:mean-canonical`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

namespace JanetCartan.PhysicalMean.OriginalCanonicalDerivative
construct_original_derivative_observation
end JanetCartan.PhysicalMean.OriginalCanonicalDerivative
