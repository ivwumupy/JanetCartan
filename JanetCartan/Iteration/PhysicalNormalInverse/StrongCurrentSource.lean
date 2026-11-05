module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrent
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongReference
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrentSourceApplication

/-!
# Actual source inputs of the same strengthened current inverse

`StrongCurrent.source_continuation` fills all20 source/measurement/coefficient
inputs of the geometric current-inverse tail using the actual `StrongSource`.
The original21 inputs end in the RAW user extra; the source and current row
both use exactly `strongCappedExtra hn userExtra`.  The source scale satisfies
both the actual inverse cap and the actual source cap.  No carrier, coefficient,
coercivity or inverse-success premise remains at this layer.

The remaining leading budgets and history-specific full leading data are the
actual outputs of task13/17 on this same strengthened initializer.  Their final
parent application is still explicit; this file is not a claim of Main.
The generic current high constants may depend on σ. Pre-σ density smallness
uses the separate actual uniform reference bounds and fixed-σ current raw
continuity, never an invalid choice of σ after a σ-dependent constant.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

apply_actual_strong_source_to_current_inverse
