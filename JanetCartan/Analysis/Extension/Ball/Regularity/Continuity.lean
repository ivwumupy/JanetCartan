module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Away
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Piecewise

/-!
# Uniform convergence and boundary matching at order zero

This is the order-zero case of the boundary-jet argument following
`app:ch_regular_base:eq:extension-collar-l2`. Absolute summability gives uniform
convergence on the closed exterior, and the zeroth moment gives the boundary value.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (p : JanetCartan.BallExtension.Parameters E)

/-- The sampling maps fix the sphere in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem radialPoint_eq_self_of_mem_sphere {x : E} (hx : x ∈ sphere p.center p.radius)
    (k : ℕ) : p.radialPoint k x = x := by
  have hn := mem_sphere_iff_norm.mp hx
  simp [radialPoint, hn, p.radius_pos.ne']

/-- Each term has its prescribed zeroth jet on the sphere, as used after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem summand_eq_smul_of_mem_sphere (a : ℕ → ℝ) (f : E → F) {x : E}
    (hx : x ∈ sphere p.center p.radius) (k : ℕ) :
    p.summand a f x k = a k • f x := by
  have hc : p.cutoff 0 = 1 := p.cutoff_eq_one le_rfl (by linarith [p.width_pos])
  simp [summand, mem_sphere_iff_norm.mp hx, hc, p.radialPoint_eq_self_of_mem_sphere hx]

/-- In the closed exterior collar, the sampling points lie in the closed ball,
including the boundary in `app:ch_regular_base:eq:extension-radial-formula`. -/
theorem radialPoint_mem_closedBall_of_scaled_lt {x : E}
    (hx : p.radius ≤ ‖x - p.center‖) {k : ℕ}
    (hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width) :
    p.radialPoint k x ∈ closedBall p.center p.radius := by
  rcases hx.eq_or_lt with he | he
  · have hb : x ∈ sphere p.center p.radius := mem_sphere_iff_norm.mpr he.symm
    rw [p.radialPoint_eq_self_of_mem_sphere hb]
    exact sphere_subset_closedBall hb
  · exact ball_subset_closedBall (p.radialPoint_mem_ball_of_scaled_lt he hk)

/-- Continuity of each term on the closed exterior, needed for the uniform
convergence argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem continuousOn_summand_closedExterior (a : ℕ → ℝ) {f : E → F}
    (hf : ContinuousOn f (closedBall p.center p.radius)) (k : ℕ) :
    ContinuousOn (fun x ↦ p.summand a f x k) {x | p.radius ≤ ‖x - p.center‖} := by
  intro x hx
  have hxc : x ≠ p.center := by
    rintro rfl
    simpa using (p.radius_pos.trans_le hx)
  have hs : ContinuousAt (fun y : E ↦ (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius)) x := by
    fun_prop
  by_cases hk : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width
  · have hr := p.radialPoint_mem_closedBall_of_scaled_lt hx hk
    have hp : p.radialPoint k ⁻¹' closedBall p.center p.radius ∈
        𝓝[{x | p.radius ≤ ‖x - p.center‖}] x := by
      filter_upwards [self_mem_nhdsWithin,
        (hs.eventually (gt_mem_nhds hk)).filter_mono nhdsWithin_le_nhds] with y hy hky
      exact p.radialPoint_mem_closedBall_of_scaled_lt hy hky
    have hfr := (hf _ hr).comp_of_preimage_mem_nhdsWithin
      (p.contDiffAt_radialPoint k hxc).continuousAt.continuousWithinAt hp
    exact (continuousWithinAt_const.mul
      (p.cutoff.continuous.continuousAt.comp hs).continuousWithinAt).smul hfr
  · have hk' : p.width / 2 < (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
      linarith [p.width_pos, le_of_not_gt hk]
    have hz : (fun y ↦ p.summand a f y k) =ᶠ[𝓝 x] (fun _ ↦ (0 : F)) := by
      filter_upwards [hs.eventually (lt_mem_nhds hk')] with y hy
      exact p.summand_eq_zero a f y k hy.le
    exact (continuousAt_const.congr hz.symm).continuousWithinAt

/-- The order-zero majorant remains valid on the sphere, for the uniform
convergence argument after `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem norm_summand_le_closedExterior (a : ℕ → ℝ) (f : E → F) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ y ∈ closedBall p.center p.radius, ‖f y‖ ≤ M) {x : E}
    (hx : p.radius ≤ ‖x - p.center‖) (k : ℕ) :
    ‖p.summand a f x k‖ ≤ |a k| * M := by
  rcases hx.eq_or_lt with he | he
  · have hb : x ∈ sphere p.center p.radius := mem_sphere_iff_norm.mpr he.symm
    rw [p.summand_eq_smul_of_mem_sphere a f hb, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf x (sphere_subset_closedBall hb)) (abs_nonneg _)
  · exact p.norm_summand_le a f hM hf he k

variable [CompleteSpace F]

/-- Uniform convergence up to the sphere at order zero in the argument following
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem tendstoUniformlyOn_summand_sum (a : ℕ → ℝ) (ha : Summable (fun k ↦ |a k|))
    (f : E → F) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y ∈ closedBall p.center p.radius, ‖f y‖ ≤ M) :
    TendstoUniformlyOn (fun N x ↦ ∑ k ∈ Finset.range N, p.summand a f x k)
      (fun x ↦ ∑' k, p.summand a f x k) atTop {x | p.radius ≤ ‖x - p.center‖} := by
  exact tendstoUniformlyOn_tsum_nat (ha.mul_right M)
    (fun k x hx ↦ p.norm_summand_le_closedExterior a f hM hf hx k)

omit [CompleteSpace F] in
/-- The zeroth moment identifies the exterior series with the input on the
sphere, as in the boundary-jet argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem tsum_summand_eq_of_mem_sphere (a : ℕ → ℝ) (ha : (∑' k, a k) = 1)
    (f : E → F) {x : E} (hx : x ∈ sphere p.center p.radius) :
    (∑' k, p.summand a f x k) = f x := by
  simp_rw [p.summand_eq_smul_of_mem_sphere a f hx]
  have hs : Summable a := by
    by_contra h
    have hz := tsum_eq_zero_of_not_summable h
    rw [ha] at hz
    norm_num at hz
  rw [hs.tsum_smul_const, ha, one_smul]

/-- Continuity of the exterior series up to the sphere, by its summable
order-zero majorant in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem continuousOn_tsum_summand_closedExterior [FiniteDimensional ℝ E]
    (a : ℕ → ℝ) (ha : Summable (fun k ↦ |a k|)) {f : E → F}
    (hf : ContinuousOn f (closedBall p.center p.radius)) :
    ContinuousOn (fun x ↦ ∑' k, p.summand a f x k) {x | p.radius ≤ ‖x - p.center‖} := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall p.center p.radius).exists_bound_of_continuousOn hf
  have hb : ∀ y ∈ closedBall p.center p.radius, ‖f y‖ ≤ max M 0 :=
    fun y hy ↦ (hM y hy).trans (le_max_left _ _)
  exact continuousOn_tsum (p.continuousOn_summand_closedExterior a hf)
    (ha.mul_right (max M 0))
    (fun k x hx ↦ p.norm_summand_le_closedExterior a f (le_max_right _ _) hb hx k)

/-- Continuity of the actual extension across the sphere: the order-zero case
of the boundary matching following `app:ch_regular_base:eq:extension-collar-l2`.
Only the absolute zeroth moment and the zeroth moment identity are required. -/
theorem continuous_extend [FiniteDimensional ℝ E] (a : ℕ → ℝ)
    (ha : Summable (fun k ↦ |a k|)) (hm : (∑' k, a k) = 1) {f : E → F}
    (hf : ContinuousOn f (closedBall p.center p.radius)) : Continuous (p.extend a f) := by
  apply continuous_if
  · intro x hx
    have hb : x ∈ sphere p.center p.radius := by
      have he : {y : E | ‖y - p.center‖ ≤ p.radius} = closedBall p.center p.radius := by
        ext y; exact mem_closedBall_iff_norm.symm
      rwa [he, frontier_closedBall _ p.radius_pos.ne'] at hx
    exact (p.tsum_summand_eq_of_mem_sphere a hm f hb).symm
  · have he : {y : E | ‖y - p.center‖ ≤ p.radius} = closedBall p.center p.radius := by
      ext y; exact mem_closedBall_iff_norm.symm
    simpa only [he, isClosed_closedBall.closure_eq] using hf
  · apply (p.continuousOn_tsum_summand_closedExterior a ha hf).mono
    apply closure_minimal
    · intro y hy
      exact (lt_of_not_ge hy).le
    · exact isClosed_le continuous_const (by fun_prop)

end JanetCartan.BallExtension.Parameters
