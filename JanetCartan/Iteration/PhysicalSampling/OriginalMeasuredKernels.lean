module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBoundsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBoundsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# The original measured row's numerical amplitude, mean and sharp bounds

Use the already constructed literal raw kernel, original source, coefficient
cutoff, measurement and full uncut response. Its compactness-based internal
bound is not substituted for the uniform prehistory amplitude budget. The
actual full-response jet profile remains its identified upstream obligation
(`app:ch_waves:eq:sampling-prefix-normal`).
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

bound_original_measured_row_amplitude
bound_original_measured_row_operator 0
bound_original_measured_row_operator 1
