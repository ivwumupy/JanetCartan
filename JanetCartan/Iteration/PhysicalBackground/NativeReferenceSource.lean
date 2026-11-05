module

public import JanetCartan.Iteration.PhysicalBackground.OriginalOuterCutoff
public import JanetCartan.Iteration.PhysicalBackground.OriginalProductSource
public import JanetCartan.Iteration.PhysicalBackground.RetainedMeasuredSource
public import JanetCartan.Iteration.PhysicalDensityContinuity.Strong
import all JanetCartan.Iteration.PhysicalBackground.OriginalProductSource
import all JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Actual PhysicalSeed protected-weight reference source before sigma

The input21 is already selected (including whichever once-only sampling/strong
caps the caller fixed). This module applies NO extra cap. It retains that
source family's native measurement radius and c_sigma, and takes task74's ONE
protected chi. The chi-dependent mean H0, X0 and measured source are freshly
formed, never borrowed from the old full-source weight or forward's distinct
Mean tuple. Its output feeds `NativeRawSeedBudget` and original-data density
admission (`app:ch_background:prop:bg-current`, `new:sec:order-of-choices`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff

realize_native_protected_reference_source
