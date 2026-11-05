module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Discrepancy
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Fixed coefficient for the two actual primary quadratures

The common discrepancy price and the dimension-only tensor reconstruction
constant precede the queried history or sample (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

bound_actual_primary_node 0
bound_actual_primary_node 1

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Cnode_nonneg
