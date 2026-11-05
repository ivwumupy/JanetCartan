module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# The actual current measured sampling prefixes before the response estimate

These are the same original source/dilation, physical finite history, current
immersion, common measurement and fixed Band/Mean profile constants. The
positive background high initial profile and the actual uncut-response profile
still belong to their producers. No second sampling event is constructed
(`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
open scoped Matrix.Norms.Frobenius

cache_original_measured_current_measurement 0
cache_original_measured_current_measurement 1
apply_original_measured_current_factory 0
apply_original_measured_current_factory 1
