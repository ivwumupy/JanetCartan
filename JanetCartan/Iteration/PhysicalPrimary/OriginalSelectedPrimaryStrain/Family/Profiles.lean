module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Phase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Amplitude
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Coefficients
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The actual primary phase and derivative factors over all admitted labels

The same ordinary phase, current Q, twice-Jacobian and full raw amplitude
are fixed independently of the later source identity. The first-mask and
negative-moment producers consume these fields (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.phase
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Q
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.A
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.B
