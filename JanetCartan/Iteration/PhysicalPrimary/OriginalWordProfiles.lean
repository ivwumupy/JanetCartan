module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordGradient
public import JanetCartan.Iteration.PhysicalPrimary.OriginalOperatorProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhaseProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalWordProfilesTemplate

/-! One common prehistory threshold for the SAME canonical current, full Q/B
profiles and physical phase profiles. The existing coefficient and phase
profiles are reused, not chosen again. The physical phase is independent of a
sector, including for an empty sector family; every coordinate profile is its
literal isometric pullback. Consumer: actual native53/50 coefficient and phase
fields and the full inverse remainder (`app:ch_response:eq:fixed-factor-transfer`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPrimary.OriginalWordProfiles

retain_original_joint_word_profiles

end JanetCartan.PhysicalPrimary.OriginalWordProfiles
