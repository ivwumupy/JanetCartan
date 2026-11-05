module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonBudgets

/-!
# The actual original finite corrected normal on the global current

The measured event kernel and the comparison kernel are identified literally.
The per-row comparisons are summed at K=Lambda with J=cutoffCount Lambda and
the exact global native39 carried by the original canonical source. The
transport constant precedes every current history and selected sample.
The subsequent same-sample and fixed-source error applications consume these
fields (`app:ch_mean_pairs:eq:mean-stage-normal-errors`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

construct_original_mean_estimate 0
construct_original_mean_estimate 1
construct_original_mean_estimate 2
construct_original_mean_estimate 3
construct_original_mean_estimate 4

#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.corrected_kernel_eq_event
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.correctedMean_eq_event_mean
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.correctedNormal
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.Ctransport
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate.normalized_sampling_error
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate.original_transport_factor
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate.original_normal_error_decay
