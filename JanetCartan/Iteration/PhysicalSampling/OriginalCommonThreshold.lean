module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication

/-!
# The original common measured/scalar threshold before histories

The single threshold applies to the actual original finite families and
Fourier amplitudes. It is an upstream numeric choice, not an application to a
successful current or a replacement for the final actual common realization
(`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

apply_actual_original_common_threshold
cache_actual_original_threshold_field 0
cache_actual_original_threshold_field 1
cache_actual_original_threshold_field 2
cache_actual_original_threshold_field 3
cache_actual_original_threshold_field 4
cache_actual_original_threshold_field 5
cache_actual_original_threshold_field 6
