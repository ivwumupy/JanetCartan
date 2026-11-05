module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongReferenceApplication

/-!
# Pre-source-scale raw bounds on the actual strengthened reference row

For `app:ch_background:prop:bg-inverse` and the current positive-background
admission, `StrongSourceGap.reference_uncorrected_raw` retains the exact two
uniform source estimates from the genuine prescribed measured-source producer.
`PhysicalSeed.SourceInverseBoundary.Kraw` and `Cfull` depend only on the original
21 inputs, BEFORE σ, v and the Sobolev order.  This supplies the reference low
density baseline using the new factor2/index1 uncut synthesis; the old density
synthesis tail is deliberately not used.

The source operator is exactly `StrongSourceGap.Vop` at the actual scale. It is
NOT the physical current-history operator. Current density admission still
needs the proved current-to-reference raw continuity at fixed σ; a generic
current estimate whose constant depends on σ cannot replace this argument.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

project_strong_reference_uncorrected_raw
