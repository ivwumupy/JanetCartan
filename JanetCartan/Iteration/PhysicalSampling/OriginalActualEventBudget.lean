module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalActualEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalActualEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication

/-! The one before-R₀ numerical budget under one original positive σ ceiling.
The same pre-frame slot can first be capped by the adjoint's original moment
tolerance; γ is bounded by that slot, the strain tolerance and both original
graph tolerances before the source scale is chosen (`new:sec:order-of-choices`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

pack_actual_original_event 0
pack_actual_original_event 1
pack_actual_original_event 2
pack_actual_original_event 3
