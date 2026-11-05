module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMeanPrecisionTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMeanCoreError
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecision
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-!
# Actual physical mean precision on the existing original final core

Apply genuine115 C1 precision and physical58 on the SAME residual, full-source
Picard count and unchanged Schwartz mean. Accuracy precedes history; the only
inputs are numerical reaches and one original final-core membership. Both core
containments are already proved, not assumed (`main:eq:mean-equation`).
-/
set_option warningAsError true
set_option Elab.async false
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
prove_original_physical_mean_precision 0
prove_original_physical_mean_precision 1
