module

public import JanetCartan.Iteration.PhysicalInverseContinuity.NativeSource
public import JanetCartan.Iteration.PhysicalInverseContinuity.MeasuredHistory
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.NativeCurrentApplication

/-! The literal original current `Vop`, with its full native zero-density
specification and the prescribed fixed-grade comparison of the *measured*
raw corrections. The parent chooses its actual leading charts; no normal,
adjoint, residual or inverse-continuity premise is passed in. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 36000
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

join_actual_native_measured_inverse
