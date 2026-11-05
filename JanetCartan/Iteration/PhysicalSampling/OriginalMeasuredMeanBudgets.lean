module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# Before-history measured mean on the actual original family

The SAME fixed current-geometry and measurement budgets chosen for the
original corrected comparison supply the actual original mean. Its Cmean is
fixed after the source scale and the uncut-response budget but before current
histories, rates, frequencies or random samples. This does not assert that the
dynamic response profile is already available
(`app:ch_waves:eq:sampling-operator-bounds`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

cache_original_measured_mean_factory
cache_original_measured_mean_budget_field 0
cache_original_measured_mean_budget_field 1
cache_original_measured_mean_budget_field 2
cache_original_measured_mean_budget_field 3
