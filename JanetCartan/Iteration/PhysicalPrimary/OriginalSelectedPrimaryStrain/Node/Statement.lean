module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.Costs
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.StatementTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Exact statement of the same primary node strain estimate

The transparent proposition keeps the original node, numerical admissions
and closed core; its proof follows separately (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_actual_primary_node_statement

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.node_strain_statement
