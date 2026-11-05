module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceLinear
public import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackground
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalIterationApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalIterationApplication
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
# The actual finite source on the one original fixed prefix

The forcing is exactly the original weighted background error. The full
uncut-auxiliary linear source and complete Hermitian quadratic source use the
same original inverse, history, sample and prefix throughout the finite run.
The selected run is the trial run at the ONE named original shift. Quantitative
convergence, source mass and physical mean completion are separate obligations,
not assumptions of these data (`app:ch_mean_pairs:eq:single-iteration`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

construct_actual_canonical_iteration 0
construct_actual_canonical_iteration 1
