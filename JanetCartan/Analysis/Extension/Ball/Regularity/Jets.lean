module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Continuity
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The individual exterior jets

The terms of `app:ch_regular_base:eq:extension-radial-formula` are smooth within
the closed exterior. This file supplies uniqueness of these one-sided jets,
including points on the sphere, for the argument after
`app:ch_regular_base:eq:extension-collar-l2`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (p : JanetCartan.BallExtension.Parameters E)

/-- Derivatives within the closed exterior are unique, including on the sphere,
so the exterior jets used after `app:ch_regular_base:eq:extension-collar-l2`
are well-defined. -/
theorem uniqueDiffOn_closedExterior :
    UniqueDiffOn ℝ {x : E | p.radius ≤ ‖x - p.center‖} := by
  intro x hx
  let c := x + (x - p.center)
  let r := ‖x - p.center‖
  have hr : 0 < r := p.radius_pos.trans_le hx
  have hc : c - p.center = (2 : ℝ) • (x - p.center) := by dsimp [c]; module
  have hxc : x - c = -(x - p.center) := by dsimp [c]; abel
  have hball : UniqueDiffOn ℝ (closedBall c r) := by
    apply uniqueDiffOn_convex (convex_closedBall c r)
    exact ⟨c, ball_subset_interior_closedBall (mem_ball_self hr)⟩
  apply (hball x (by
    apply mem_closedBall_iff_norm.mpr
    rw [hxc, norm_neg])).mono
  intro y hy
  have hdist : ‖c - p.center‖ ≤ ‖y - c‖ + ‖y - p.center‖ := by
    calc
      ‖c - p.center‖ = ‖(c - y) + (y - p.center)‖ := by congr 1; abel
      _ ≤ ‖c - y‖ + ‖y - p.center‖ := norm_add_le _ _
      _ = ‖y - c‖ + ‖y - p.center‖ := by rw [norm_sub_rev c y]
  have hcr : ‖c - p.center‖ = 2 * r := by rw [hc, norm_smul]; simp [r]
  rw [hcr] at hdist
  have hy' := mem_closedBall_iff_norm.mp hy
  change p.radius ≤ ‖y - p.center‖
  change p.radius ≤ r at hx
  linarith

/-- Each term is smooth within the closed exterior, without assuming any
ambient extension of the input. This is the individual-term regularity needed
for the boundary-jet argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem contDiffOn_summand_closedExterior (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x ↦ p.summand a f x k) {x | p.radius ≤ ‖x - p.center‖} := by
  intro x hx
  have hxc : x ≠ p.center := by
    rintro rfl
    simpa using (p.radius_pos.trans_le hx)
  have hn : ContDiffAt ℝ ∞ (fun y ↦ ‖y - p.center‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hxc)
  have hs : ContDiffAt ℝ ∞ (fun y ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x :=
    contDiffAt_const.mul (hn.sub contDiffAt_const)
  by_cases hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width
  · have hr := p.radialPoint_mem_closedBall_of_scaled_lt hx hk
    have hp : p.radialPoint k ⁻¹' closedBall p.center p.radius ∈
        𝓝[{x | p.radius ≤ ‖x - p.center‖}] x := by
      filter_upwards [self_mem_nhdsWithin,
        (hs.continuousAt.eventually (gt_mem_nhds hk)).filter_mono nhdsWithin_le_nhds] with y hy hky
      exact p.radialPoint_mem_closedBall_of_scaled_lt hy hky
    have hfr := (hf _ hr).comp_of_preimage_mem_nhdsWithin x
      (p.contDiffAt_radialPoint k hxc).contDiffWithinAt hp
    exact (contDiffAt_const.mul (p.cutoff.contDiff.contDiffAt.comp x hs)).contDiffWithinAt.smul hfr
  · have hk' : p.width / 2 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
      linarith [p.width_pos, le_of_not_gt hk]
    have hz : (fun y ↦ p.summand a f y k) =ᶠ[𝓝 x] (fun _ ↦ (0 : F)) := by
      filter_upwards [hs.continuousAt.eventually (lt_mem_nhds hk')] with y hy
      exact p.summand_eq_zero a f y k hy.le
    exact ((contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hz).contDiffWithinAt

end JanetCartan.BallExtension.Parameters
