module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The original primary Q and twice-Jacobian over all source labels

These are the same actual current projection and source derivative used by
the uncut response. Their uniform profiles feed the first mask and negative
moments (`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_actual_primary_source_family 7
publish_actual_primary_source_family 8

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Q
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.A
