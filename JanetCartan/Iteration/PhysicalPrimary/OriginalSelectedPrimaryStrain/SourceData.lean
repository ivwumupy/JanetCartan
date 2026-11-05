module
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceDataTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The same original primary tensor, inverse input and smooth discrepancy

Consumer: `main:eq:primary-strain`. Compact tensor membership and source
support are actual consequences of the original raw wave. No source cutoff is
applied twice, and the existing uncut inverse is retained in the discrepancy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_original_primary_source_data 0
publish_original_primary_source_data 1
publish_original_primary_source_data 2
publish_original_primary_source_data 3
publish_original_primary_source_data 4
publish_original_primary_source_data 5

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.tensor
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.input
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.discrepancy
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.discrepancy_smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData.input_support
