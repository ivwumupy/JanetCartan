module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Inputs
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Profiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.ZeroExtension

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The actual uniform primary source family

The fixed selected33+N prefix precedes all the late data in the original
primary source, including its sample and real or imaginary quadrature.
Consumer: the first mask and inverse remainder in `main:eq:primary-strain`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.historyMap
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.input
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.phase
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.support
