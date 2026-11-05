module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceQuadratic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticRealization
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearProfilesTemplate
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
# The actual high quadratic estimate on the one original selected sample

The shared actual primitive realization is used unchanged. The finite prefix,
all annuli and cross-shell terms, one Fourier normalization, global Q0, and the
original selected shift are the same as in the constructed quadratic operator.
Only the supplied source's legitimate profile remains an analytic premise.
The static numerical moment/reach guards belong to the pre-source selector;
no successful iteration or desired output estimate is assumed
(new:eq:source-bound, app:ch_mean_pairs:eq:block-bilinear).
-/

public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open JanetCartan.PhysicalMean

run_meta do
  OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun params fields => do
    OriginalCanonicalQuadraticSourceProfilesTemplate.publishSourceProfile params fields
