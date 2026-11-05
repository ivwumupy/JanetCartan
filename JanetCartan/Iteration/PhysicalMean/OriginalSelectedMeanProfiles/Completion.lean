module
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
# Actual completed-mean bound before the physical cutoff

Apply the original normal-buffer, initialized-field/strain, normalized-target
and full sampled-self producers to the SAME selected completed mean. This
executes only the completed cNorm profile; the physical cutoff consumer is a
separate leaf. The original selected52, fixed J, N, initial/current numerical
gates and exact prehistory convolution coefficient are unchanged
(`main:eq:mean-normal-field`, `main:eq:mean-size`).
-/
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
construct_original_selected_mean_profile 4
