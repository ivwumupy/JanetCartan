module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Realization
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Profiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Low norms of the same once-measured primary input

The original reduced-wave identity and fixed derivative price give the
uniform source norm independently of first-mask localization. This is the
low-norm input to the original residual estimate (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_primary_first_mask 8
prove_actual_primary_first_mask 9

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.sourceNorms
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.source_polynomial
