module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputBridgeApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputBridgeApplication
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
# Exact actual individual and weighted-aggregate input identities

The unweighted individual annular input is exactly the actual An adjoint on the
SAME global Q0 source. Its Gprefix action is exactly the physical G action on
the actual final wide input. The weighted aggregate is recorded separately as
R.adjoint Q0 e with93's SAME input isometry and adjoint identity. No division by
a zero sample weight or additional sqrt μ occurs (`main:eq:old-canonical`,
`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

construct_actual_canonical_input_bridge 0
construct_actual_canonical_input_bridge 1
construct_actual_canonical_input_bridge 2
construct_actual_canonical_input_bridge 3
