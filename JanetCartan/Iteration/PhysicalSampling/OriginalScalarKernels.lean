module

public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarFamily
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalScalarKernelsApplication

/-!
# Actual current scalar kernels for the one original common event

These names expose the two kernels literally present in the already-proved
actual scalar current continuation, using the SAME retained low-frame proof.
Their analytic bounds are direct projections of that continuation. The raw
kernel has the original masks and full finite-rate phase; its existing carrier
cut is removed only on the literal original weight plateau
(`new:eq:amplitude-test`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

cache_original_scalar_kernel_frame
cache_original_scalar_current_kernel_field 0
cache_original_scalar_current_kernel_field 1
cache_original_scalar_current_kernel_field 2
cache_original_scalar_current_kernel_field 3
cache_original_scalar_current_kernel_field 4
