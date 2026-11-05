module

public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles
public meta import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles

/-!
# The original leading-minus-corrected continuum contribution

The first retained primitive is the genuine corrected-minus-leading derivative
error on the full original parent sigma-cover. It retains its actual colored
rate rather than absorbing it into the total-amplitude cost. The remaining
measured tensor, normalized colored continuum, and source-profile estimates
must use this SAME original data (new:eq:mean-source,
app:ch_waves:eq:WKB-amplitude-difference).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

retain_original_parent_true_rate_error
publish_original_leading_error_cost 0
publish_original_leading_error_cost 1
publish_original_leading_error_cost 2
publish_original_leading_error_cost 3
publish_original_weighted_leading_error
