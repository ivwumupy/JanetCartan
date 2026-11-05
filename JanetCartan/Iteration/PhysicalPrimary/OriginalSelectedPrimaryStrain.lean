module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTransfer

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalActualTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Primary strain for the identical original full-source physical field

This supplies `main:eq:primary-strain` in paper-v2 §§10, 15, and 16 for
`OriginalFullSourcePhysicalPrimary.field54`, with its fixed selected data,
finite complete-forcing Picard count and external amplitude. The coefficient
is fixed before history and target; no analytic success premise is supplied
to the final `strain_bound` consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

instantiate_primary_strain_from_original_nodes

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Cstrain
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Cstrain_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_bound
