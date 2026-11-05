module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularForwardTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularForwardTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
/-!
# The original raw angular differential as the full forward annular sum

The unprefixed and original fixed-prefix formulas use the SAME raw field,
ordinary carrier, source chart, annuli and unchanged input. Each exact
proposition is checked separately from its proof to keep the original kernel
budget; no new premise or different mathematical statement is introduced
(`main:eq:primary-strain`, `main:eq:lag-strain`).
-/
check_actual_raw_angular_forward 1
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual.unprefixed_forward_statement
