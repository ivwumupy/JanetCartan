module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPhaseMargins
public import JanetCartan.Iteration.PhysicalSampling.HistoryBudgets
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalScalarHistoryApplication

/-!
# Actual prehistory scalar numerical choices

The numerical map and normal-gap budgets use the exact original source-dilated
reference. They precede every history and are independent of density and full
corrected-response budgets. The common threshold includes the existing original
current-frame threshold (`app:ch_seed:setup:seed-current`,
`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open Set Metric
namespace JanetCartan.PhysicalSampling
open PhysicalSeed

/-- The original coefficient ball, not a fresh working radius, contains each
original state ball and is compactly inside the existing source phase domain. -/
theorem original_scalar_coefficient_ball {n : ℕ} (hn : 5 ≤ n) :
    IsCompact (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) ∧
    closedBall (0 : Euclidean n) (OriginalBoundary.b hn) ⊆ ball 0 (OriginalBoundary.R hn) ∧
    ∀ a, closedBall (0 : Euclidean n) (OriginalBoundary.T hn a).data.localReference.stateRadius ⊆
      closedBall 0 (OriginalBoundary.b hn) :=
  ⟨isCompact_closedBall _ _, closedBall_subset_ball (OriginalBoundary.b_lt_R hn),
    PhysicalInitialization.original_frameBall_subset hn⟩

namespace OriginalScalarHistory
cache_original_scalar_reference
cache_original_scalar_budget_field 0
cache_original_scalar_budget_field 1
cache_original_scalar_budget_field 2
cache_original_scalar_budget_field 3
cache_original_scalar_budget_field 4
cache_original_scalar_budget_field 5
cache_original_scalar_graph_threshold
cache_original_scalar_common_threshold
end OriginalScalarHistory
end JanetCartan.PhysicalSampling
