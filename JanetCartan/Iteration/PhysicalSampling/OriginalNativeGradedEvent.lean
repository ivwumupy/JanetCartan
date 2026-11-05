module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEvent
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication

/-!
# Original one-shift sampling with no remaining analytic profile inputs

The actual source53 and native weak38 produce qualitative joint regularity;
the original complete finite inverse produces the uncontracted derivative
matrix jets on the whole working compact. No replacement response, scalar
test, small output cutoff or choice of a second ξ occurs. Both deviations,
bare and weighted physical tests, geometry/mass/counts and χ² quadrature
are preserved on the same issued realization (`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

prove_original_uncontracted_sampling_jets
apply_unconditional_original_sampling_event
