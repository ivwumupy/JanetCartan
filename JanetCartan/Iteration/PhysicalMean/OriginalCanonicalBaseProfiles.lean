module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseBudgets
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfilesTemplate

/-!
# Actual original initializer and FULL strain on the physical cutoff buffer

Supply the real all-order raw regularity and source grade profile at reserve
n+1, on the SAME original raw/current/chi/X0. Reuse the existing closed-b
base-plus-FULL-strain producer and ball-R smoothness, then restrict to the
verified physical cutoff buffer. No derivative of a coarse base norm is used.
The initial numerical gate Sbase <= R0 remains explicit. This is the INITIAL
Vbase, not the later positive-source correction Q0r or completed mean.
Consumer: the original physical mean profile (`main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric JanetCartan
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

retain_original_base_inputs 0
retain_original_base_inputs 1
retain_original_base_inputs 2
retain_original_base_inputs 3
specialize_original_base_wide_profile 0
specialize_original_base_wide_profile 1
specialize_original_base_wide_profile 2
specialize_original_base_wide_profile 3
specialize_original_base_wide_profile 4
