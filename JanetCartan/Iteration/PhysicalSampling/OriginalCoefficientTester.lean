module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarEventInputs
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterApplication

/-!
# A genuine common-cutoff tester for the original aggregate scalar norm

The SAME native operator from the common sampled event has the original
row-dependent scalar cutoffs. Its contractive output restriction by the
ALREADY selected coefficient cutoff has *one* cutoff in its exact moment
kernel. The input remains the native inner sampled shell measure, with its
original half-derivative factor, mask, phase, weights, and prefix. The bound
on this restricted tester costs neither a sample count nor another event.

Only the scalar TESTER is restricted. There is no claim here that the full
response or an uncut physical corrector is supported in the four-radius ball.
Coefficient support for each downstream amplitude, outer-label transport and
the separate individual bare tester retain their own obligations
(`new:eq:amplitude-test`, `app:ch_mean_pairs:eq:block-normal`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

apply_original_scalar_coefficient_tester
