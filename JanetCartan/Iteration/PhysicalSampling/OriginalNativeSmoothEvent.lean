module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEvent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalInitialSourceApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalResponseSmooth
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication

/-!
# Genuine source53 and weak38 smoothness on the original sampling event

The source's fixed unscaled budget is reused at offset 16 with size σ. The
admitted row is the actual protected density, not a replacement low source.
Both native thresholds, the static source family and the single original
history are reached together before this uncut joint proof. The only analytic
field remaining at this stage is the *quantitative* derivative-amplitude jet,
not ordinary regularity (`app:ch_response:cor:current-atoms`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2800000

supply_original_joint_uncut_smoothness
apply_original_event_of_quantitative_uncut_jets
