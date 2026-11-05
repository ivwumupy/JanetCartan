module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfiles.Completion
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfileBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfilesApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanFieldProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianEstimates
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMean
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-!
# Actual completed and Schwartz mean true-R profiles

This staged execution applies actual110 normal-buffer,117 full initialized
W/full strain,14 normalized tensor and116 full sampled self to ONE completed
mean and the SAME original physical cutoff. Both final58 profiles have only
selected52,hAux,N,hFullW,hBuffer,hTargetStage,s; no analytic success premise or
N-dependent initial threshold (`main:eq:mean-size`, `main:prop:mean`).
-/
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
construct_original_selected_mean_profile 5
