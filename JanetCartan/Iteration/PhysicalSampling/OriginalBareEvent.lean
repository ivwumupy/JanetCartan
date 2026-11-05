module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareAtPoint
public import JanetCartan.Iteration.PhysicalSampling.OriginalSobolevEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterCoefficientTester
public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterQuadrature
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# Both physical scalar testers on the one original positive sampling event

Choose the bare-admitting frame and cap before source selection. For the same
physical map and exact shift, preserve the measured/scalar deviations,
quadrature, geometry and Sobolev amplitude test, the outer-weighted aggregate
and its very own individual bare rows (`app:ch_mean_pairs:eq:block-fields`).
The same exterior measure also retains its physical amplitude test and all
count, mass and separation bounds. The positive event's actual high initial
profile and joint uncut-response profiles remain explicit upstream obligations;
this application neither assumes a successful sample nor closes those producers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
apply_original_bare_positive_event
