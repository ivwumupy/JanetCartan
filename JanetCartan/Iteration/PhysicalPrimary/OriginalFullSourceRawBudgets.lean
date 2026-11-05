module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourceRawApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-!
# Fixed budget for the actual full-source before-B derivative field

The common all-order D_N budget enters before history, target or smoothing.
The genuine raw forward matrix is used, not the corrected derivative matrix
and not the scalar Fourier-mass budget (`main:eq:primary-strain`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_actual_full_source_raw 0
publish_actual_full_source_raw 1
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles.Csource
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles.Csource_nonneg
