module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawBaselineProfileTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
/-!
# Original-row budget for the before-response raw baseline matrix

The coefficient is fixed before every initial scale, history, target, source,
sampling prefix and label. The finite sum runs over original rows only; there
is no sampled-family cardinality (`main:eq:primary-strain`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_actual_raw_baseline 0
publish_actual_raw_baseline 1
publish_actual_raw_baseline 2
#print axioms JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.Cbaseline
#print axioms JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.Cbaseline_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.row_le_Cbaseline
