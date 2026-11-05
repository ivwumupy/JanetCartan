module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
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
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# The actual final whole-source physical wave

The physical-field identity uses the same original source53/graph42 and the
already proved original response-integral continuity. All its spatial jets are
the original corrected-atom integrals, including order zero, with the unchanged
conic detector, high-frequency cutoff and literal Fourier density.

The final baseline-plus-correction field then uses the original fixed-prefix
finite source's **unweighted** component input. Its original positive baseline
and zero-safe angular factor are unchanged. The single chosen native-event
shift is reused; sqrt of the sample weight remains external to the complete
physical field. No recut, alternate response, input normalization or new sampler
is introduced (`app:ch_lag:eq:lag-recurrence`, `main:eq:primary`).

This file publishes actual field data, integral identities and old-chart
smoothness independently of the sharp-envelope construction. Its jet-mass
consequence retains the actual density integral on the right; it does not assert
the pending fixed-K Picard mass estimate or the final physical Sobolev profiles
(`main:eq:primary-fixed-scales`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

publish_original_native_whole_physical_jets
publish_original_native_final_combined_wave
publish_original_native_selected_combined_wave
