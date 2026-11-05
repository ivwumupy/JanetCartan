module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairCoreTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairEstimates
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedSelfIdentity
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates.Identities
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The unchanged actual aggregate-primary/full-self residual retaining the
original coefficient mass. Consumer: `main:prop:pairs`, `main:eq:pair-error`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

identify_original_selected_pair_core 1

#print axioms JanetCartan.PhysicalPairs.OriginalSelectedPairCore.mass_lag
