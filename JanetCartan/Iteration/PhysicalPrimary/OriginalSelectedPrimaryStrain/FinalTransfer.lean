module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.Statement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTransferTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Same-field physical primary strain from the original node estimates

This deduction consumes exactly the existing node statement at every original
sample. The final root supplies its actual producer; this conditional result
alone does not close primary strain (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_primary_strain_from_original_nodes

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_of_original_nodes
