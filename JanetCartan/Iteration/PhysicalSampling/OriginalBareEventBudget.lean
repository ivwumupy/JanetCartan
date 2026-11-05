module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareFamily
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication

/-! # Original bare/admitted outer event constants before the history

The individual tester and the native positive two-mask sampler retain one
prehistory frame, cap and numerical threshold. Separating these constants lets
the physical source choose the true high scalar bound before any sample exists
(`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

choose_original_bare_event_budget 0
choose_original_bare_event_budget 1
choose_original_bare_event_budget 2
choose_original_bare_event_budget 3
choose_original_bare_event_budget 4
choose_original_bare_event_budget 5
