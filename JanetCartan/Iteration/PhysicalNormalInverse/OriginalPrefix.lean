module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalPrefixApplication
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfiles

/-!
# The actual rounded zero-endpoint carrier normal

`OriginalPrefix.of_native` retains the supplied unmeasured Vop and its ENTIRE
native inverse predicate. It identifies the continuum leading prefix with the
rounded squared-mask normal of the SAME carrier after its original common
measurement restriction. It includes both real quadratures, the exact factor
four and the literal squared Fourier constant. It does not replace the augmented
inverse normal, remove the common measurement or alter image/exterior channels.

All qualitative continuity, compatibility, support, graph, plateau, detector and
coordinate inputs are deduced from the original native data. The original
carrier mass is not coupled to the smaller common measurement scale, and the
sampler radius is chosen only once (`app:ch_waves:eq:sampling-prefix-normal`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
open scoped ContDiff Matrix.Norms.Frobenius

apply_actual_original_carrier_prefix

#print axioms JanetCartan.PhysicalNormalInverse.OriginalPrefix.native_leading_continuity
#print axioms JanetCartan.PhysicalNormalInverse.OriginalPrefix.of_native
