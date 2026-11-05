module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! The literal SAME whole raw source observation, for the exact source
composition (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.Template.publish 1

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Values.source_observation
