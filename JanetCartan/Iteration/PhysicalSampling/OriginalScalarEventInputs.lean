module

public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarKernels
public import JanetCartan.Iteration.PhysicalSampling.OriginalEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
public import JanetCartan.Iteration.PhysicalSampling.OriginalAmplitude
public import JanetCartan.Iteration.PhysicalForwardMean.OriginalScalar
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalScalarEventInputsApplication

/-!
# Actual scalar inputs of the single original common event

These fields retain the original finite index, literal scalar kernels, carrier
weights and convolved-box window. The sharp constant and summed continuum mean
constant are the finite sums already chosen before histories. Each row's rate
admission follows from the ONE `OriginalMargins.ε` used by the actual rate
producer. The existing carrier-cut identity transfers the proved bounds to the
raw scalar family.

This module supplies the scalar side of the event; it neither assumes a scalar
norm nor chooses a successful sample. The actual measured family must still be
joined before `exists_threshold_original_common_scalar_native_of_amplitude`
is instantiated ONCE (`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

cache_original_scalar_kernel_family_field 0
cache_original_scalar_kernel_family_field 1
cache_original_scalar_family_cut_sharp
cache_original_scalar_family_cut_mean
cache_original_scalar_family_raw_inputs
cache_original_scalar_family_amplitude_field 0
cache_original_scalar_family_amplitude_field 1
cache_original_scalar_family_amplitude_field 2
cache_original_scalar_family_native_kernel
