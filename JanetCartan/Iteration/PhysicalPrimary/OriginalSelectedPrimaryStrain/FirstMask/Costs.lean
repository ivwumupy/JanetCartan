module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMaskTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Fixed prices for the actual primary source profiles

The original twice-Jacobian and full raw amplitude prices give one common
derivative price. The once-measured source theorem chooses its norm price
from those fixed profiles before every admitted label. Its actual source
bound is proved separately after realization (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_primary_first_mask 0
prove_actual_primary_first_mask 1
prove_actual_primary_first_mask 5
prove_actual_primary_first_mask 6
prove_actual_primary_first_mask 7

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Cmask
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.sourceNormCost_nonneg
