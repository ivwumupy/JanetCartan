module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventBudget
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBoundsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# The one original event uses the actual protected positive density

The background source cap is met before σ, and the native density's true
threshold before R₀. The existing native label density and all its finite-low
conditions are applied, not quantified as assumptions. The three outstanding
high-profile conclusions are explicit (`app:ch_background:prop:bg-current`,
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

put_native_positive_labels_in_original_event
