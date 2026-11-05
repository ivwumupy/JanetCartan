module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Prescribed
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongReference
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.StrongApplication

/-!
# Actual fixed-source full-row strong adjoint continuity

`StrongRaw.exists_source_adjoint_tolerance` takes the original 21 callback
parameters, their fixed source scale and its own interval proof, and a regular
reference datum. It uses the original source's actual uncorrected carrier,
normal solution and raw adjoint estimate. All selected geometry is projected
from the very same fixed physical boundary, not supplied via a perturbation
interface. The remaining current fields are the actual native forward and
adjoint realizations and full order-one estimate when the current row is
constructed (`app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow CarrierSobolev ContinuumRow.CanonicalCarrier
open ContinuumRow.NormalizedSelection ContinuumNormal.ActualConstruction

realize_strong_raw_fixed_source_adjoint

end JanetCartan.PhysicalInverseContinuity
