module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialData
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication

/-!
# The original positive sampler with the actual high initial field

The actual source-density producer fixes an **unscaled** `initialC` before
history. The sample row uses exactly `σ * initialC` for the SAME native labels.
The density-inverse operator threshold and original sample threshold are met
at one R₀. The higher source/response use can retain its requested stronger
initial reserve while the sampler uses `16 + rawSliceParameterOrder n`.
Only the joint smoothness and jet profile of the actual uncut response remain
in the event application (`new:eq:amplitude-test`, `app:ch_response:cor:current-atoms`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

apply_original_event_with_native_initial
