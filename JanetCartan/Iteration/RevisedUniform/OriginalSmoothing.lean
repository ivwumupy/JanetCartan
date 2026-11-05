module

public import JanetCartan.Iteration.PhysicalSmoothing
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public meta import JanetCartan.Iteration.RevisedUniform.OriginalSmoothingTemplate

/-!
# Actual original smoothing on the native inverse defect core

The separate smoothing domain has the SAME χ₂ half-radius core D and the
native χ₂ PDE ball as chart. It does not change the original flat reference's
domain. The existing finite-moment physical producer supplies a fixed target
interval and compact support before accuracy/history, all low and high tails,
symmetry and normalized-source profiles on the actual induction core. There is
no small-defect premise outside D and no additional normalization matrix choice
(`main:lem:smoothing`, `main:eq:smoothing-low`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RevisedUniform.OriginalSmoothing

/-- The native support certificate gives a strict upper bound for the actual
inverse plateau radius, not a selected smoothing radius (`main:lem:smoothing`). -/
theorem bump_inner_lt_coefficient_bound {d : ℕ} (χ : ContDiffBump (0 : Euclidean (d+1)))
    {b : ℝ} (hsupport : tsupport (χ : Euclidean (d+1) → ℝ) ⊆ ball 0 b) : χ.rIn < b := by
  have hOut : 0 < χ.rOut := χ.rIn_pos.trans χ.rIn_lt_rOut
  obtain ⟨x, hx⟩ := exists_norm_eq (Euclidean (d+1)) hOut.le
  have hxs : x ∈ tsupport (χ : Euclidean (d+1) → ℝ) := by
    rw [χ.tsupport_eq]
    simpa only [mem_closedBall, dist_zero_right, hx] using (le_refl χ.rOut)
  have hOutb : χ.rOut < b := by
    simpa only [mem_ball, dist_zero_right, hx] using hsupport hxs
  exact χ.rIn_lt_rOut.trans hOutb

/-- The independent local domain passed to the checked physical smoother:
core is the native χ₂ half-radius core and chart is its PDE ball. This does not
modify the original FlatReference.domain (`main:lem:smoothing`). -/
def bumpSmoothingDomain {d : ℕ} (χ : ContDiffBump (0 : Euclidean (d+1)))
    (b : ℝ) (hb : b < 1/2)
    (hsupport : tsupport (χ : Euclidean (d+1) → ℝ) ⊆ ball 0 b) : LocalDomain where
  coreRadius := χ.rIn/2
  chartRadius := χ.rIn
  coreRadius_pos := half_pos χ.rIn_pos
  coreRadius_lt_chartRadius := half_lt_self χ.rIn_pos
  chartRadius_lt_half := (bump_inner_lt_coefficient_bound χ hsupport).trans hb

/-- Both smoothing sets are literal native radii, and the whole smoothing
chart is in the genuine χ₂ plateau neighborhood (`main:lem:smoothing`). -/
theorem bumpSmoothingDomain_spec {d : ℕ} (χ : ContDiffBump (0 : Euclidean (d+1)))
    (b : ℝ) (hb : b < 1/2)
    (hsupport : tsupport (χ : Euclidean (d+1) → ℝ) ⊆ ball 0 b) :
    let D := bumpSmoothingDomain χ b hb hsupport
    D.core (d+1) = closedBall (0 : Euclidean (d+1)) (χ.rIn/2) ∧
      D.chart (d+1) = ball (0 : Euclidean (d+1)) χ.rIn ∧
      ∀ y ∈ D.chart (d+1), (χ : Euclidean (d+1) → ℝ) =ᶠ[𝓝 y] (fun _ ↦ 1) := by
  intro D
  refine ⟨rfl, rfl, ?_⟩
  intro y hy
  exact χ.eventuallyEq_one_of_mem_ball hy

end JanetCartan.RevisedUniform.OriginalSmoothing

construct_actual_original_smoothing_domain
apply_physical_smoothing_to_original_core
