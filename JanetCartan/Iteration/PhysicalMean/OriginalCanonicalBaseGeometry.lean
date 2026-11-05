module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseProfilesTemplate

/-!
# The unchanged original physical cutoff and its verified norm buffer

Recover the SAME original inverse bump and source-dilated reference from the
native full-response graph. Its physical cutoff support has radius 5a/6 and is
contained in the fixed norm buffer 11a/12, inside the original chart a<b<R.
No physical cutoff is reselected or restricted to the positive-background core.
Consumer: the original Schwartz mean and its true physical Sobolev profile
(`main:eq:mean-normal-field`, `main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric JanetCartan
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

construct_original_base_physical_geometry 0
construct_original_base_physical_geometry 1
construct_original_base_physical_geometry 2
construct_original_base_physical_geometry 3
construct_original_base_physical_geometry 4
construct_original_base_physical_geometry 5
construct_original_base_physical_geometry 6
