module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.GraphTemplate

/-! The original graph tensor comparison used by both quadratures of the
actual primary (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

derive_original_graph_tensor_strain

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.graph_tensor_strain_le_discrepancy
