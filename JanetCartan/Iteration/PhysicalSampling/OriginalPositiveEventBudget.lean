module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication

/-!
# Admit the original native background at the unique sampler scale and threshold

The cap is intersected before σ. The subsequent numerical maximum admits the
actual native labels and the actual measured/scalar samplers before R₀, with
no sample or physical history as input (`app:ch_background:prop:bg-current`,
`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

admit_original_positive_event_scale
choose_original_positive_event_threshold 0
choose_original_positive_event_threshold 1
choose_original_positive_event_threshold 2
choose_original_positive_event_threshold 3
