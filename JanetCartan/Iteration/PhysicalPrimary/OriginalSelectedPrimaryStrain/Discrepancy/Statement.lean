module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.NegativeMoments
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DiscrepancyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Exact statement of the uniform original source discrepancy bound

This transparent proposition retains the same field, closed core, frequency
and quantifiers. Its proof is published separately (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

bound_actual_primary_discrepancy 4

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.discrepancy_exists_statement
