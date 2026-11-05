module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.Native
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedCore

/-!
# The actual primary strain is controlled by its original source discrepancies

This is the same-field transfer in `paper-v2.tex`, `main:eq:primary-strain`.
The literal native full primary, its original full uncut response and both
source quadratures are retained. Its exact selected and native proposition
heads unfold to the displayed inequality. The comparison has no source-decay or
response-success hypothesis; the independent localization producer supplies
the quantitative bounds on the two displayed discrepancies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.selected_node_strain_le_discrepancies
