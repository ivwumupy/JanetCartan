module

public import JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
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
# A single actual-stage sampler, conditional only on its original profile producers

For the same original physical history, the literal corrected measured kernels
and half-weighted scalar kernels feed one simultaneous concentration theorem.
The numerical threshold, mask budgets, graded estimates and detector/mean
applications are not assumptions. The positive-density/initial-profile and
uncut joint response inputs must still be discharged by their original physical
producers before this proves an unconditional stage (`new:eq:amplitude-test`,
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

retain_original_event_measured_kernel
apply_original_joint_event_of_profiles
