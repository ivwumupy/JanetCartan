module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Statement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Statement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Actual full-source primary L² at the revised stage exponent

Order zero of the genuine actual physical norm producer, existing physical
Plancherel, and the original initial numerical threshold give the SAME field's
spatial L² bound. Its coefficient is chosen before history, target, smoothing
and external amplitude. The exact proposition and unchanged proof term are
checked in separate leaves without any new analytic premise or resource limit.
Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles.hPL2`
(`main:eq:primary-fixed-scales`, `main:eq:final-Cr`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_actual_full_source_primary_L2 1
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.L2_profiles
