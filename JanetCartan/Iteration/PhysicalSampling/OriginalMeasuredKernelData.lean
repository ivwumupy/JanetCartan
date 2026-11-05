module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication

/-!
# The literal original measured kernel, before its numerical estimates

Retain the actual corrected amplitude on the same full uncut response and
original physical current. Its compact cut-amplitude continuity, support and
mask are derived here; only genuine joint smoothness of the full response is
still an input. The prehistory quantitative mean and band bounds consume this
same named kernel in `OriginalMeasuredKernels`
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

prove_original_cut_corrected_amplitude_continuous
retain_original_measured_row_kernel_field 0
retain_original_measured_row_kernel_field 1
retain_original_measured_row_kernel_field 2
