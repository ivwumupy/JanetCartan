module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalRetainedProfilesApplication

/-!
# Five coefficient profiles for the identical original current row

`OriginalRetained.Budgets` selects its constants on the fixed31 original
current prefix, one actual selected index and the initial-density profile
budget, before the physical history. `OriginalRetained.application` supplies
its exact retained tuple, phase and forward/inverse maps automatically.

`OriginalRetained.positive_continuation` additionally discharges the initial
smoothness, C14 norm and lower bound using the SAME scalar cap's universal C15
certificate. Its remaining density conditions and high derivative profile
belong to the actual positive-density construction. This module does not assert
the complete corrected-normal comparison
(`app:ch_waves:eq:colored-normal-comparison`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

cache_original_retained_profiles
