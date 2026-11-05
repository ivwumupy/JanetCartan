module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalAmbientSupport
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSolverSupport
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponseCompactTemplate

/-! # Native compact support of the globally uncut physical response
Both the unique smooth solver and the same admitted tensor response inherit
the existing original output support. No output cutoff is inserted; the later
Schwartz packaging consumes these exact support certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
retain_original_full_response_compact_part 0
