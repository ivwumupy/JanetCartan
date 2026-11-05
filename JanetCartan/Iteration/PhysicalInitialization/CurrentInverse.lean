module

public import JanetCartan.Iteration.PhysicalInitialization.CurrentLeading
public meta import JanetCartan.Iteration.PhysicalInitialization.CurrentInverseTemplate

/-!
# The actual original source/current inverse

The same original source prefix, source/current caps, physical history scale and
numerical leading-frame tolerance construct every current chart and every native
leading input. Uniform inverse constants precede the history. All density tests,
actual row realizations, exact inverse identities and regularity outputs of the
native current theorem are retained, not replaced with a successful-inverse
hypothesis. Consumers: task33 same-reference raw continuity and task24's positive
background, `app:ch_background:prop:bg-inverse`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 18000000

cache_original_current_inverse_budgets
apply_original_current_inverse_leading
