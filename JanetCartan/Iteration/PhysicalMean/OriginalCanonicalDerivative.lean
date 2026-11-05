module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalObservation
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves

/-!
# Original observation data for the whole-source canonical derivative

The original common source cutoff is fixed before history and is one as a germ
on the full original measurement support. It is only the auxiliary periodic
extension of the whole-wave derivative: the physical wave and its already
admitted whole source are unchanged (`app:ch_mean_pairs:defn:mean-canonical`).

The native G application consumes the original53/graph42 whole-wave producer's
selected-cell smoothness. Its application and the quantitative fixed-K mean
construction remain task14 obligations; the following original-data geometry
alone is not an existence theorem for the mean field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

namespace JanetCartan.PhysicalMean.OriginalCanonicalDerivative
construct_original_whole_source_derivative
construct_original_full_angular_derivative
end JanetCartan.PhysicalMean.OriginalCanonicalDerivative
