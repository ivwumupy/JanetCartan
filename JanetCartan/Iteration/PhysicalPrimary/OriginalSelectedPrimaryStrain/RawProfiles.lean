module
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Original complete raw primary amplitude at the true stage scale

The actual raw baseline and complete-forcing source profiles are combined on
the same whole source chart, with a coefficient fixed before history and
target. Consumer: the first-mask localization in `main:eq:primary-strain`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_original_primary_raw_profile 0
publish_original_primary_raw_profile 1
publish_original_primary_raw_profile 2
publish_original_primary_raw_profile 3
publish_original_primary_raw_profile 4

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles.Craw
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles.Craw_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles.amplitude
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles.profile
