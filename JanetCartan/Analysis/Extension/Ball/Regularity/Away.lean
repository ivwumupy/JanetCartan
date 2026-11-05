module

public import JanetCartan.Analysis.Extension.Ball.Construction

/-!
# Regularity away from the boundary sphere

Local finiteness of the formula in `app:ch_regular_base:eq:extension-radial-formula`
gives smoothness on the exterior. The cutoff transition is treated using a larger
collar on which all sampling points still lie strictly inside the original ball.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (p : JanetCartan.BallExtension.Parameters E)

/-- The sampling maps in `app:ch_regular_base:eq:extension-radial-formula`
are smooth away from the center. -/
theorem contDiffAt_radialPoint (k : ℕ) {x : E} (hx : x ≠ p.center) :
    ContDiffAt ℝ ∞ (p.radialPoint k) x := by
  have hd : ContDiffAt ℝ ∞ (fun y : E ↦ y - p.center) x :=
    contDiffAt_id.sub contDiffAt_const
  have hn := hd.norm ℝ (sub_ne_zero.mpr hx)
  exact contDiffAt_const.add
    ((contDiffAt_const.sub (contDiffAt_const.mul (hn.sub contDiffAt_const))).div hn
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)) |>.smul hd)

/-- On a slightly larger collar than the cutoff support, sampling still lands
inside the ball; this includes cutoff endpoints in the radial formula
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem radialPoint_mem_ball_of_scaled_lt {x : E}
    (hx : p.radius < ‖x - p.center‖) {k : ℕ}
    (hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width) :
    p.radialPoint k x ∈ ball p.center p.radius := by
  have hs : 0 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) :=
    mul_pos (by positivity) (sub_pos.mpr hx)
  have hi : 0 < p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    linarith [p.width_lt, p.radius_pos]
  have hn : 0 < ‖x - p.center‖ := p.radius_pos.trans hx
  rw [mem_ball_iff_norm, radialPoint, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hi hn), div_mul_cancel₀ _ hn.ne']
  linarith

/-- Each individual term of `app:ch_regular_base:eq:extension-radial-formula`
is smooth outside the closed ball, even where the cutoff vanishes. -/
theorem contDiffAt_summand_exterior (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : p.radius < ‖x - p.center‖) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun y ↦ p.summand a f y k) x := by
  have hxc : x ≠ p.center := by
    rintro rfl
    simpa using (p.radius_pos.trans hx)
  have hn : ContDiffAt ℝ ∞ (fun y ↦ ‖y - p.center‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hxc)
  have hs : ContDiffAt ℝ ∞ (fun y ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x :=
    contDiffAt_const.mul (hn.sub contDiffAt_const)
  by_cases hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width
  · have hr := p.radialPoint_mem_ball_of_scaled_lt hx hk
    have hfr : ContDiffAt ℝ ∞ f (p.radialPoint k x) :=
      hf.contDiffAt (mem_of_superset (isOpen_ball.mem_nhds hr) ball_subset_closedBall)
    exact (contDiffAt_const.mul (p.cutoff.contDiff.contDiffAt.comp x hs)).smul
      (hfr.comp x (p.contDiffAt_radialPoint k hxc))
  · have hk' : p.width / 2 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
      linarith [p.width_pos, le_of_not_gt hk]
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hs.continuousAt.eventually (lt_mem_nhds hk')] with y hy
    exact p.summand_eq_zero a f y k hy.le

/-- Near each exterior point the formula in
`app:ch_regular_base:eq:extension-radial-formula` is one fixed finite sum. -/
theorem eventually_extend_eq_sum (a : ℕ → ℝ) (f : E → F) {x : E}
    (hx : p.radius < ‖x - p.center‖) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x,
      p.extend a f y = ∑ k ∈ Finset.range N, p.summand a f y k := by
  let t := (‖x - p.center‖ - p.radius) / 2
  have ht : 0 < t := half_pos (sub_pos.mpr hx)
  obtain ⟨N, hN⟩ := p.exists_truncation ht
  refine ⟨N, ?_⟩
  have hc : ContinuousAt (fun y : E ↦ ‖y - p.center‖ - p.radius) x := by fun_prop
  have htx : t < ‖x - p.center‖ - p.radius := by dsimp [t]; linarith
  filter_upwards [hc.eventually (lt_mem_nhds htx)] with y hy
  exact p.extend_eq_sum a f (by linarith) (hN _ hy.le)

/-- The extension is smooth at every exterior point by local finiteness of
`app:ch_regular_base:eq:extension-radial-formula`. No coefficient hypotheses
are needed for this assertion away from the sphere. -/
theorem contDiffAt_extend_exterior (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : p.radius < ‖x - p.center‖) : ContDiffAt ℝ ∞ (p.extend a f) x := by
  obtain ⟨N, hN⟩ := p.eventually_extend_eq_sum a f hx
  exact (ContDiffAt.sum (fun k (_ : k ∈ Finset.range N) ↦
    p.contDiffAt_summand_exterior a hf hx k)).congr_of_eventuallyEq hN

/-- In the interior the extension in
`app:ch_regular_base:eq:extension-radial-formula` inherits the input's smoothness. -/
theorem contDiffAt_extend_interior (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) {x : E}
    (hx : ‖x - p.center‖ < p.radius) : ContDiffAt ℝ ∞ (p.extend a f) x := by
  have hb : closedBall p.center p.radius ∈ 𝓝 x :=
    mem_of_superset (isOpen_ball.mem_nhds (mem_ball_iff_norm.mpr hx)) ball_subset_closedBall
  apply (hf.contDiffAt hb).congr_of_eventuallyEq
  filter_upwards [hb] with y hy
  exact p.extend_eq_on_closedBall a f hy

/-- All possible nonsmooth points of
`app:ch_regular_base:eq:extension-radial-formula` lie on the original sphere. -/
theorem contDiffOn_extend_compl_sphere (a : ℕ → ℝ) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiffOn ℝ ∞ (p.extend a f) (sphere p.center p.radius)ᶜ := by
  intro x hx
  have hx' : ‖x - p.center‖ ≠ p.radius := by simpa [mem_sphere_iff_norm] using hx
  rcases lt_or_gt_of_ne hx' with hi | he
  · exact (p.contDiffAt_extend_interior a hf hi).contDiffWithinAt
  · exact (p.contDiffAt_extend_exterior a hf he).contDiffWithinAt

end JanetCartan.BallExtension.Parameters
