module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.NativeStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The retained-background differential theorem, on the SAME original
outer-node regularity operands, proves the stored native equality without
converting the raw atom or its full derivative amplitude.
Consumer: `Actual.baseline_factor` (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template.publishNative false

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.native_factor
