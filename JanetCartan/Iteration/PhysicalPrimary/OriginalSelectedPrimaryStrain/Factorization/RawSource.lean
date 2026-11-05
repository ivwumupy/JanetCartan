module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The actual pre-response field for the original primary strain

The native raw construction is specialized to the already selected source,
component adjoint and original sample.  Its baseline is unscaled and its angular
summand keeps the whole input.  The imported native identity identifies the unchanged corrected wave with
the complex source correction of this raw sum (`main:eq:primary-strain`).

These are actual field identities and regularity, not a residual estimate.  The
raw derivative factorization and first-mask estimate are separate consumers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

check_actual_raw_source_identity 0
check_actual_raw_source_identity 1
check_actual_raw_source_identity 2

#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.raw
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.raw_smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.source
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.combined_eq_corrected_raw
