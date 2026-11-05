module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainCosts
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Exact primary strain statement for the same full-source physical field

This transparent proposition keeps all58 original arguments, the same field54
and the literal revised power. The final root supplies its proof. The separate
statement changes no hypothesis or conclusion (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_full_source_primary_strain 3

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_statement
