module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.FrequencyStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity.FrequencyStatement

/-! The observed residual retains the same undoubled original carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentityTemplate.publishProof true

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.history_frequency_eq
