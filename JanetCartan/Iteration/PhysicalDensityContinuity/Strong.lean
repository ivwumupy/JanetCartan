module

public import JanetCartan.Iteration.PhysicalDensityContinuity.Prescribed
public import JanetCartan.Iteration.PhysicalInverseContinuity.Strong
public meta import JanetCartan.Iteration.PhysicalDensityContinuity.StrongApplication

/-!
# Actual original-source physical density mean continuity

The generated theorem applies the primitive mean construction to the exact
original23 strengthened-source tuple, with its original zero-density chart,
source contraction and angular mask. All original static geometry is replayed
from the checked134 application. No new source selection or second extra cap
is introduced. The SAME compact parameter weight and its three primitive
certificates remain universal; the mean and coefficient continuity are proved.
Consumer: the original current measured-source low/high transfer in
`app:ch_background:prop:bg-current`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalDensityContinuity

realize_strong_source_density_mean_tolerance

end JanetCartan.PhysicalDensityContinuity
