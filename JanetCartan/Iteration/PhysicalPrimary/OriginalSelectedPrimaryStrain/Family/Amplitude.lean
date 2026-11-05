module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The full original raw amplitude over both primary quadratures

This is the unscaled raw baseline plus the same full-forcing source. The
imaginary label rotates only this amplitude by minus I; its derivative
profile feeds the first mask (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_actual_primary_source_family 9

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.B
