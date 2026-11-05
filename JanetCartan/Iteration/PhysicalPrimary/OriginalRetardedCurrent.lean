module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalIncidence
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrentTemplate

/-!
# The same original current at the common incidence/frame/momentum margin

Use the already constructed graph/frame source interval at the ONE actual
incidence margin. Its prehistory threshold gives both the original normalized
inverse and the additional full-window frame/momentum certificates. The frame
is defined independently of a sector, including when the finite sector set is
empty. No current, source scale, reference or inverse is selected again.

Consumer: the actual whole-source retarded/residual and solver instantiations,
then `actual_finite_residual_word_reserved_bounds_of_one_step`
(`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPrimary.OriginalRetardedCurrent

retain_original_current_at_incidence_margin

end JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
