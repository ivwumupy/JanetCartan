module

public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# The actual original unscaled positive Hermitian baseline

Retain the literal native positive scalar, full response, measurement and actual
spatial carrier from the original saved50 event. The baseline is NOT multiplied
by the inner incidence/detector weight or its coefficient cutoff. The original
exterior weight is kept separately; no sample, measure or source is reselected.

Consumer: original weighted background quadrature and the full physical mean
(`app:ch_waves:eq:background-quadrature`, `app:ch_mean_pairs:eq:comparison-input`).
The weighted physical identification is proved separately below, not assumed by
these data getters.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

retain_original_positive_background_data 0
retain_original_positive_background_data 1
retain_original_positive_background_data 2
retain_original_positive_background_data 3
retain_original_positive_background_data 4
retain_original_positive_background_data 5
retain_original_positive_background_data 6
retain_original_positive_background_data 14
retain_original_positive_background_data 15
retain_original_positive_background_data 16
