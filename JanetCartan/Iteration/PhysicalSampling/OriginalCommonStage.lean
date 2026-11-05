module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageBudget
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication

/-!
# A genuine common initial scale for all original rows

The numerical maximum is taken before history/stage. It reaches the scalar
history threshold, all measured current43 thresholds, and the coarse/fine
admission needed for the actual simultaneous event and its continuum
comparison (`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

apply_original_common_stage_rates
