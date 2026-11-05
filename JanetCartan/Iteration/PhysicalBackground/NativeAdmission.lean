module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensity
public import JanetCartan.Iteration.PhysicalBackground.NativeRawSeedBudget
public meta import JanetCartan.Iteration.PhysicalBackground.NativeAdmissionTemplate

/-!
# Actual same-current density admission from the two proved raw half-budgets

Take the ONE protected outer weight and freshly formed X0 from task76, retain
`Original.rawCurrent`, and specialize the already chosen `NativeDensity.v`.
The finite order is `2*(n+1)+14`, fixed before sigma. The original current raw
comparison and actual reference half-budget prove the required raw smallness;
no raw-smallness, positivity or density-class premise is introduced.

Sigma remains universal inside the constructed cap. The parent may further
intersect that cap with the SAME-row regular-solver and other original caps;
no inequality between unrelated caps is asserted here. The original history
threshold is retained before the history (`app:ch_background:prop:bg-current`,
`app:ch_background:eq:bg-density-input`). All-high quantitative initial profiles
and exact physical cancellation remain separate parent obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff

realize_native_current_density_admission
