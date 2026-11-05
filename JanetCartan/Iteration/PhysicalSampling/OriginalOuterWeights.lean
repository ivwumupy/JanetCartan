module

public import JanetCartan.Iteration.PhysicalBackground.OriginalOuterCutoff
public import JanetCartan.Iteration.PhysicalSampling.OriginalExternalWeights
public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeightsTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeightsTemplate

/-!
# Actual outer physical weights on the original22 sampler

The input labels, original inner mask and sampling cap are exactly those of
`OriginalWeights`. The original21 outer cutoff is task74's ONE static cutoff:
its entire support lies in the original product collar and the protected strict
parameter cube. It is not chosen again here. Apply the sampling cap and then
the strong cap ONCE before passing that selected21 to the cutoff producer.

The external weight is literally χ² on the same coordinates. One common cube
is chosen before any physical history, current inverse, mesh or sampling event.
The old inner sample set is unchanged on this enlarged cube; its nonzero
labels embed into the outer set on the SAME global shifts. The exact μ and
√μ identities include zero weights and supply the finite normal benchmark
transfer. The unscaled full positive background retains the OUTER weight;
no baseline mean or whole physical quadratic field is identified here.

Consumers: `OriginalWeightBridge`, the actual original positive initialization
and `app:ch_background:eq:bg-affine-mean`,
`app:ch_waves:eq:sampling-prefix-normal`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

construct_original_outer_weights
