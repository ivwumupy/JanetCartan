module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Representative
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The same original phase over every admitted primary source label

The global representative is the slice of the original joint choice at the
original outer node. It supplies the first mask and negative moments without
any new phase choice (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_actual_primary_source_family 5

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.phase
