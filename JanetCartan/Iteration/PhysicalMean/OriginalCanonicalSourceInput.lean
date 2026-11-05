module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputApplication
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
# Actual final input of the original finite source run

The physical input is unweighted: the original WeightedSynthesis multiplies
the complete background-plus-correction wave by sqrt μ externally ONCE.
The original component adjoint already contains the fixed Fourier scalar;
none is inserted here. The input prefix and Picard operators stay fixed
before the step count (`app:ch_mean_pairs:defn:mean-canonical`).

These are actual DATA. Quantitative source convergence and the finite native
moment still have to be instantiated for the resulting source; neither is
assumed as a successful-mean or Fourier-mass premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

construct_actual_canonical_input 0
construct_actual_canonical_input 1
construct_actual_canonical_input 2
construct_actual_canonical_input 3
