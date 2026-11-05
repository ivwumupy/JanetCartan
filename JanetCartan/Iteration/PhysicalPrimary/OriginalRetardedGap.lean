module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrent
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedGapTemplate

/-! Actual signed full-source angular gaps and the original transported graph
momentum at the SAME common margin/current. No bare-frequency substitution is
made for the adjoint. Consumer: native full-source retarded0/1 and solver/residual
letter applications (`app:ch_response:eq:fixed-factor-transfer`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPrimary.OriginalRetardedGap

retain_actual_original_source_gap

end JanetCartan.PhysicalPrimary.OriginalRetardedGap
