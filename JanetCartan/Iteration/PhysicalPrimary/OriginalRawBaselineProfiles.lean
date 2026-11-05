module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawBaselineBudgets
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
/-!
# Actual unscaled raw baseline jets on the unchanged original chart

The baseline is literally the before-response fullDerivativeAmplitude at the
SAME outer node, with no sample weight or inner angular factor. Its global data
requires no nonzero-weight proof. On the whole original source chart, the
original OUTER nonzero admission gives smoothness and all q jets bounded by
Cbaseline44(q)*currentCoefficientScale^q. Inner angular-zero labels are retained.

This is the baseline input to the separate raw derivative factorization and
first-mask strain estimate, not a proof of either conclusion itself
(`main:eq:primary-strain`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_actual_raw_baseline 3
publish_actual_raw_baseline 4
#print axioms JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.baseline
#print axioms JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles.baseline_profile
