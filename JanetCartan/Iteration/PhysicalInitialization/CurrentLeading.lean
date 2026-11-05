module

public import JanetCartan.Iteration.PhysicalInitialization.SuppliedLeading
public import JanetCartan.Iteration.PhysicalInitialization.LeadingInverseGeometry
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongCurrentSource
public meta import JanetCartan.Iteration.PhysicalInitialization.CurrentLeadingTemplate

/-!
# Actual same-source leading inputs at the existing scalar cap

Use the original30 source/current inputs plus the numerical original leading
frame tolerance. The raw extra callback is capped only inside the original
current/source construction. Its scalar budget fixes `Mscalar = σ*Cscalar` and
`mscalar = σ*sqrt(1/2)`, before the history. All retained leading objects are
constructed on the SAME source dilation, not assumed.

The subsequent actual current-inverse application consumes these cells; this
module alone is not the complete current inverse or Main.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

@[expose] public noncomputable section
namespace JanetCartan.PhysicalInitialization

/-- The current inverse's fixed low reserve includes the original leading
fourteen derivatives (`app:ch_background:prop:bg-inverse`). -/
theorem leading_reserve_le_canonical_low_order (n : ℕ) :
    14 ≤ ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n := by
  simp only [ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder]
  omega

/-- The literal density lower bound is positive at the same chosen source
contraction; no lower scalar norm is assumed (`app:ch_background:prop:bg-inverse`). -/
theorem positive_leading_scalar_lower_bound {σ : ℝ} (hσ : 0 < σ) :
    0 < σ * Real.sqrt (1 / 2) := mul_pos hσ (by positivity)

end JanetCartan.PhysicalInitialization

cache_actual_current_leading
cache_actual_selected_leading
