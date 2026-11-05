module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
/-!
# Exact differential of the actual unscaled raw baseline

The original retained-leading differential theorem is applied to the same
outer node and raw amplitude. The identical proposition and proof are checked
separately under the original kernel budget; no analytic premise is added
(`main:eq:primary-strain`, `app:ch_waves:eq:individual-representation`).
-/
check_actual_raw_baseline_differential 1
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual.baseline_factor_statement
