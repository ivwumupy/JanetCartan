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
# Fixed budgets of the actual original initializer

Reuse NativeBaseProfiles at reserve zero with the SAME original native raw,
rCoeff, source cutoff and tangent initializer. Sbase is its original fieldS,
not a new choice and not a later-stage gate. All constants precede R0/history.
Consumer: actual initializer AND full-strain profiles (`main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric JanetCartan
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

retain_original_base_budget 0
retain_original_base_budget 1
retain_original_base_budget 2
retain_original_base_budget 3
retain_original_base_budget 4
retain_original_base_budget 5
