module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.DiscrepancyStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.DiscrepancyStatement

/-! The observed residual is the same named source field (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentityTemplate.publishProof false

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.observed_discrepancy_eq
