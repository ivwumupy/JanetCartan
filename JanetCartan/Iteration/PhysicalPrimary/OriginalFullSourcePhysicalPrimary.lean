module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The actual full-source physical primary norm producer

Instantiate the frozen source synthesis with the genuine canonical complete-
forcing Picard mass, through the native scalar bridge, on the same field and
single sample. Its physical H^q coefficient is fixed before history, target,
smoothing and external amplitude. The named proposition and proof are checked
in separate leaves without changing the statement or proof term. This closes
only the primary norm, not primary strain (`main:eq:primary-fixed-scales`).
Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_full_source_physical_primary 2
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.physical_profiles
