module

public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairProfilesTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairEstimates
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Nonnegative costs of the actual original signed correction

The integer profiles in `OriginalStepEstimates.Components` use the genuine
nonnegative lag and size coefficients. Publish these independently of the
real-order extension of `main:eq:pair-high-size`; their original producers
and static quantifier order are unchanged (`main:thm:step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

derive_original_selected_pair_profile 0
derive_original_selected_pair_profile 1

#print axioms JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles.Clag_nonneg
#print axioms JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles.Csize_nonneg
