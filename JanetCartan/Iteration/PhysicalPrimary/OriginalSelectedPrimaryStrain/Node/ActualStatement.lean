module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.Statement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.ActualStatementTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The identical original node statement at the actual fixed coefficient

Both sides retain the original aggregate's full node, core and decay. The
equality only folds the already defined Cnode (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

identify_actual_primary_node_statement

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.uniform_node_statement_eq
