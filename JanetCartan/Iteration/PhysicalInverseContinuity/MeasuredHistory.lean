module

public import JanetCartan.Iteration.PhysicalInverseContinuity.History
public import JanetCartan.Iteration.PhysicalInverseContinuity.StrongDatum
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.MeasuredHistoryApplication

/-!
# Fixed-grade raw difference on the original measured physical histories

The unchanged finite retained mean, exact source class, same tested normal,
strong-vector adjoint and finite high reserve are all realized on the same
prefix. The only remaining current clauses are the native full inverse and
its own adjoint realization, never a hypothesis of raw continuity.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option maxRecDepth 30000

open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow ContinuumRow.CanonicalCarrier CarrierSobolev

apply_actual_measured_source_to_history

end JanetCartan.PhysicalInverseContinuity
