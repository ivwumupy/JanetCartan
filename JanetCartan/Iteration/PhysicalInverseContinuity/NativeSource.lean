module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrentSource
public meta import JanetCartan.Iteration.PhysicalInverseContinuity.NativeCurrentApplication

/-! The **original** current inverse constants retained before any history or
requested current-v-reference accuracy. They may depend on the fixed final
contraction; none is ever used to select it. The uniform reference constants
remain the separate pre-contraction source estimates. -/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 26000
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

prepare_actual_native_measured_inverse
