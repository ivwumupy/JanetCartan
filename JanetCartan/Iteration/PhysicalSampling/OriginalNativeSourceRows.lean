module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialData
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication

/-!
# The original full-source rows on the strengthened shared initial reserve

The genuine unscaled fixed `initialC` is shifted by 16 exactly once per row;
its size factor σ is retained separately for the posthistory source. The
original strain tolerance, native strong/leading/current inputs and each
original39 threshold are in the numerical construction. All rows are met by a
single threshold fixed before a response budget or R₀
(`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2800000

fix_original_native_source_rows 0
fix_original_native_source_rows 1
fix_original_native_source_rows 2
fix_original_native_source_rows 3
fix_original_native_source_rows 4
fix_original_native_source_rows 5
fix_original_native_source_rows 6
