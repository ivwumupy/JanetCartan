module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFractionalProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Actual mean Sobolev size at every real nonnegative order

Apply the lossless existing physical Fourier split to the genuinely proved
integer profile of the SAME physicalMean54, original full source, ONE cutoff
count and Picard count. The coefficient is the existing early integer cost
at zero plus its value at the ceiling of the requested order. The exponent
remains exactly `R ^ r`, not `R ^ ⌈r⌉₊`, and no new initial/stage threshold or
analytic input is introduced (`main:eq:mean-size`).
-/
set_option warningAsError true
set_option Elab.async false
construct_original_selected_mean_real_profile
#print axioms JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles.physicalMean_real_sobolev_profile
