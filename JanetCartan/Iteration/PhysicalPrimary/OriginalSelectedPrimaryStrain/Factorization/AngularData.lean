module
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
/-! The SAME original full-angular raw field and its source-chart smoothness,
including zero angular labels, before the first-mask estimate
(`main:eq:primary-strain`). -/
check_actual_raw_angular 0
check_actual_raw_angular 3
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual.raw_angular
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual.raw_angular_smooth_on_source
