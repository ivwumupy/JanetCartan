module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCaps
public import JanetCartan.Iteration.PhysicalSampling.OriginalDirection
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalAdmissionApplication

/-!
# Actual selected rows admit the one pre-source sampler

Apply the original selector ONCE with `strongCappedExtra` of the minimum of the
user's original buffers and the sampling buffers. Every published theorem uses
that exact selected row and parent. The original reference prefix is unchanged.
No selected parent from another callback is identified with it.

The root, spatial/angular caps, scalar sharp/mean continuation, common κ/ψ
plateaus, exact carrier support and complete factor-four scalar cutoff collar
are all obtained by kernel-checked applications of the existing proofs. No
sampling success, scalar norm, or corrected-field estimate is assumed.
The actual current primary-profile and one-common-event applications remain
explicit producer obligations (`new:sec:order-of-choices`,
`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalAdmission
realize_original_sampling_admission
end JanetCartan.PhysicalSampling.OriginalAdmission
