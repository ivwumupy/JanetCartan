module

public import JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public import JanetCartan.Iteration.PhysicalNormalInverse.PrescribedTolerance
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongToleranceApplication

/-!
# Arbitrarily small actual current/source normal difference

`StrongSource.exists_history_normal_tolerance` has the original29 strong source
parameters, then ε and hε. All chosen source geometry, σ, masks and source carrier
operators are exactly those of `StrongSource.source_continuation`; the numerical
comparison gaps alone are reduced. Its threshold precedes all density/history
inputs. Its continuation accepts the actual current coefficient formula and the
actual carrier test action, so no identification of independently chosen rows is
left to the caller. The fixed exterior cancels exactly.

The source argument is the already selected extra, i.e. `strongCappedExtra hn
userExtra` when paired with `StrongCurrent`. The CURRENT inverse keeps its
original gap via the separate ordinary source continuation. This tolerance leaf
does not replace that gap by ε or reselect the source initializer.

Consumer: task33's current/reference normal-inverse and strong raw transfer in
`new:sec:order-of-choices`. No moving-row operator-norm continuity is asserted.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

apply_actual_strong_source_normal_tolerance
