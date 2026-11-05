module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.Costs
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Fixed coefficient for the original sampled primary strain

The original square-root sampling budget and actual node discrepancy price
define Cstrain before every history, target and amplitude. The complete-forcing
Picard count and requested accuracy are fixed (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_full_source_primary_strain 0
prove_actual_full_source_primary_strain 1

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Cstrain
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Cstrain_nonneg
