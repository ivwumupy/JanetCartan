module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMargins
public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.PhysicalFrameAdmission
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalPhaseMarginsApplication

/-!
# Actual original current phase margins for the common sampler

The original signed regular producer supplies the actual globally extended
current stress. Its same-source `Graph.current_frame_margin` is transferred to
the raw physical stress by the already proved germ equality on each original
state ball. All four retained sampler tolerances then follow from the fixed
numerical condition `γ ≤ OriginalMargins.δ`, chosen BEFORE source dilation.

No physical current stress bound, phase success, alternate reference, or new
source selector is a premise of the generated actual-current conclusions
(`new:sec:order-of-choices`, `app:ch_seed:setup:seed-current`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalSampling
open PhysicalSeed ProjectedStressFrame ProtectedFlow

/-- The existing original state-domain buffer transfers a global extended
frame margin to the raw stress on every original state ball. The actual producer
is applied immediately below, so its bound is not an extra current hypothesis. -/
theorem original_raw_frame_margin_of_extended {n N : ℕ} (hn : 5 ≤ n)
    (ext : BallExtension.Parameters (Euclidean n)) (hext : ext.center = 0)
    (hradius : ext.radius = OriginalBoundary.b hn)
    {F : Euclidean n → Euclidean N} {γ : ℝ}
    (hmargin : ∀ K : Set (Euclidean n), cNorm K 6
      (extendedProjectedStress ext F - fun _ ↦ cubeStress n) < γ)
    (a : (a : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount a)) :
    cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.T hn a).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < γ := by
  rw [CanonicalAtomRealization.cNorm_projectedStress_sub_eq_extended_on_stateBall
    (OriginalBoundary.T hn a) ext hext (by
      simpa only [hradius] using OriginalBoundary.stateDomain_subset_ball hn a) F 6]
  exact hmargin _

namespace OriginalPhaseMargins
realize_original_current_sampling_phase_margins
end OriginalPhaseMargins
end JanetCartan.PhysicalSampling
