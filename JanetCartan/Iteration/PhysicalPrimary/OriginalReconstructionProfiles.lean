module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponse
public import JanetCartan.Iteration.PhysicalPairs.Coefficients
public import JanetCartan.Iteration.PhysicalPrimary.OriginalReconstructionJoint
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalReconstructionProfilesTemplate

/-!
# Actual physical-history coefficients for the uncut primary reconstruction

The native physical Schwartz history supplies the value, derivative and source
coefficient profiles of `completedVariationComplex_joint_response_graded`.
Their common threshold and nonnegative profile are chosen before the history,
with the literal original reference and the same finite map as the uncut
ambient response. The numerical reserve is paid separately from the inverse's
finite-word reserve (`app:ch_response:eq:response-reconstruction-grading`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

construct_original_physical_reconstruction_profiles
