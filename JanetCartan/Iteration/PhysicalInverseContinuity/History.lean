module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Strong
public import JanetCartan.Iteration.PhysicalInverseContinuity.Upgrade
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongTolerance
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.HistoryApplication

/-!
# Common fixed-source inverse and physical-history thresholds

At the literal zero-density source operator, set the accuracy of the tested
normal, strong adjoint and measured residual from the real direct-sum high
reserve. The source gap and its original half-gap remain unchanged. All
constants and thresholds are fixed before the first admissible history.
Consumer: the physical zero-density comparison in `app:ch_background:prop:bg-normalized`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 18000000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow CoerciveInverse CarrierSobolev ContinuumRow.CanonicalCarrier

prepare_actual_source_raw_history
apply_actual_source_raw_history

end JanetCartan.PhysicalInverseContinuity
