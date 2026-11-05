module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication

/-!
# Prehistory measured finite sums and literal amplitude budgets

These constants use the fixed source scale, five actual retained profiles,
and positive initial/response profile budgets indexed by the same finite row
set. The family constants precede all variable currents, rates and shifts
(`app:ch_waves:thm:sampling`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

cache_original_measured_family_bound 0
cache_original_measured_family_bound 1
cache_original_measured_family_kernel_field 0
cache_original_measured_family_kernel_field 1
cache_original_measured_family_kernel_field 2
cache_original_measured_family_kernel_field 3
