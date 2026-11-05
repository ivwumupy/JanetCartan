module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Localization
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Norms

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # The primary first mask for the actual full-forcing source

Every input is supplied by the fixed original construction. The first-mask
and source-norm constants precede all labels (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.full_profile
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.first_mask
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.sourceNorms
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.source_polynomial
