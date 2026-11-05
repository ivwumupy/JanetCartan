module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourceRawBudgets
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourceRawApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-!
# Genuine raw full-forcing source jets at the true current scale

The SAME before-B raw source field has global smoothness, its original support,
and Csource_N(s) h R^s bounds on every physical set. Every source-profile input
is supplied by the actual full-forcing CommonD_N run through s+n+2. The original
fixed cutoff, sample, source inverse, mask and phases are unchanged. This is the
raw-source input to `main:eq:primary-strain`, not the separate baseline,
derivative factorization or first-mask conclusion.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_actual_full_source_raw 2
publish_actual_full_source_raw 3
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles.field
#print axioms JanetCartan.PhysicalPrimary.OriginalFullSourceRawProfiles.source_profile
