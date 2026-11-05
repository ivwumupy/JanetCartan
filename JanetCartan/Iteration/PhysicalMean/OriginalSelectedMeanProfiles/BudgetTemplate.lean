module
public import JanetCartan.Iteration.PhysicalMean.CompletedMeanPrimitiveProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedNormalizedTargetProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionBufferProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularity
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Stable prerequisites of the original mean coefficients

The static coefficient publisher needs only these existing primitive, target,
normal-buffer and regularity interfaces. Its costs and their nonnegativity
are independent of the actual completed-field profile execution. Retaining
that dependency boundary lets corrections to the execution metadata reuse
the checked coefficients (`main:eq:mean-size`). No declaration, formula or
choice is changed by this import leaf.
-/
