module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Away
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Geometry of the radial sampling collar

These are the geometric and integrability prerequisites for the substitution in
`app:ch_regular_base:eq:extension-collar-l2`. No quantitative integral estimate is
asserted in this module.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E]
  (p : Parameters E)

/-- The open sampling collar for the `k`th term of
`app:ch_regular_base:eq:extension-collar-l2`. -/
def radialCollar (k : ℕ) : Set E :=
  {x | p.radius < ‖x - p.center‖ ∧
    (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) < p.width}

/-- A compact enlargement of the sampling collar in
`app:ch_regular_base:eq:extension-collar-l2`. -/
def closedRadialCollar (k : ℕ) : Set E :=
  {x | p.radius ≤ ‖x - p.center‖ ∧
    (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) ≤ p.width}

/-- The collar used in `app:ch_regular_base:eq:extension-collar-l2` is open. -/
theorem isOpen_radialCollar (k : ℕ) : IsOpen (p.radialCollar k) :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.sub continuous_const)) continuous_const)

/-- Closed collar enlargement for `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialCollar_subset_closedRadialCollar (k : ℕ) :
    p.radialCollar k ⊆ p.closedRadialCollar k :=
  fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩

/-- The sampling collar stays away from the singular center in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem ne_center_of_mem_closedRadialCollar {k : ℕ} {x : E}
    (hx : x ∈ p.closedRadialCollar k) : x ≠ p.center := by
  intro h
  have := p.radius_pos.trans_le hx.1
  simp [h] at this

/-- The collar has a fixed bounded enclosure, uniformly in the dyadic index;
see `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem closedRadialCollar_subset_closedBall (k : ℕ) :
    p.closedRadialCollar k ⊆ closedBall p.center (p.radius + p.width) := by
  intro x hx
  rw [mem_closedBall_iff_norm]
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hscaled : ‖x - p.center‖ - p.radius ≤
      (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    nlinarith [sub_nonneg.mpr hx.1]
  linarith [hx.2]

variable [InnerProductSpace ℝ E]

/-- The enlarged collar is compact in finite dimension, as used to justify
integrability in `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem isCompact_closedRadialCollar [FiniteDimensional ℝ E] (k : ℕ) :
    IsCompact (p.closedRadialCollar k) := by
  apply (isCompact_closedBall p.center (p.radius + p.width)).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_const.mul
        ((continuous_id.sub continuous_const).norm.sub continuous_const)) continuous_const))
  exact p.closedRadialCollar_subset_closedBall k

/-- Exact sampled radius in `app:ch_regular_base:eq:extension-collar-l2`. The
width assumption ensures the radial coefficient is positive, even at the ends. -/
theorem norm_radialPoint_sub_center_of_mem_closedRadialCollar {k : ℕ} {x : E}
    (hx : x ∈ p.closedRadialCollar k) :
    ‖p.radialPoint k x - p.center‖ =
      p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
  have hn : 0 < ‖x - p.center‖ := p.radius_pos.trans_le hx.1
  have hr : 0 < p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) := by
    linarith [hx.2, p.width_lt, p.radius_pos]
  rw [radialPoint, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hr hn), div_mul_cancel₀ _ hn.ne']

/-- Closed collar sampling lands in the closed ball in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialPoint_mem_closedBall_of_mem_closedRadialCollar {k : ℕ} {x : E}
    (hx : x ∈ p.closedRadialCollar k) :
    p.radialPoint k x ∈ closedBall p.center p.radius := by
  rw [mem_closedBall_iff_norm, p.norm_radialPoint_sub_center_of_mem_closedRadialCollar hx]
  have : 0 ≤ (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hx.1)
  linarith

/-- The existing strict sampling lemma gives the image inclusion needed for
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialPoint_image_radialCollar_subset_ball (k : ℕ) :
    p.radialPoint k '' p.radialCollar k ⊆ ball p.center p.radius := by
  rintro _ ⟨x, hx, rfl⟩
  exact p.radialPoint_mem_ball_of_scaled_lt hx.1 hx.2

omit [InnerProductSpace ℝ E] in
/-- A uniform lower bound for the tangential radial scale in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialPoint_scale_ge_one_third {k : ℕ} {x : E}
    (hx : x ∈ p.closedRadialCollar k) :
    (1 : ℝ) / 3 ≤
      (p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) / ‖x - p.center‖ := by
  have hn : 0 < ‖x - p.center‖ := p.radius_pos.trans_le hx.1
  have hb := p.closedRadialCollar_subset_closedBall k hx
  rw [mem_closedBall_iff_norm] at hb
  apply (le_div_iff₀ hn).mpr
  linarith [hx.2, p.width_lt]

/-- The radial sampling map is injective on the collar. This supplies the
injectivity hypothesis of change of variables in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem injOn_radialPoint_radialCollar (k : ℕ) :
    InjOn (p.radialPoint k) (p.radialCollar k) := by
  intro x hx y hy hxy
  have hx' := p.radialCollar_subset_closedRadialCollar k hx
  have hy' := p.radialCollar_subset_closedRadialCollar k hy
  have hnorm := congrArg (fun z ↦ ‖z - p.center‖) hxy
  rw [p.norm_radialPoint_sub_center_of_mem_closedRadialCollar hx',
    p.norm_radialPoint_sub_center_of_mem_closedRadialCollar hy'] at hnorm
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  have heq : ‖x - p.center‖ = ‖y - p.center‖ := by
    have : (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius) =
        (2 : ℝ) ^ k * (‖y - p.center‖ - p.radius) := by linarith
    have := mul_left_cancel₀ hpow this
    linarith
  have hscale : (p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) /
      ‖x - p.center‖ ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) (p.radialPoint_scale_ge_one_third hx'))
  simp only [radialPoint, ← heq] at hxy
  have := (smul_right_injective E hscale) (add_left_cancel hxy)
  exact sub_left_injective this

/-- Integrability of a continuous input pulled back to a collar, without any
quantitative pullback assumption (`app:ch_regular_base:eq:extension-collar-l2`). -/
theorem integrableOn_comp_radialPoint_radialCollar
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ] {g : E → ℝ}
    (hg : ContinuousOn g (closedBall p.center p.radius)) (k : ℕ) :
    IntegrableOn (g ∘ p.radialPoint k) (p.radialCollar k) μ := by
  have hc : ContinuousOn (p.radialPoint k) (p.closedRadialCollar k) := by
    intro x hx
    exact (p.contDiffAt_radialPoint k (p.ne_center_of_mem_closedRadialCollar hx)).continuousAt.continuousWithinAt
  exact ((hg.comp hc (fun _ hx ↦
    p.radialPoint_mem_closedBall_of_mem_closedRadialCollar hx)).integrableOn_compact
      (p.isCompact_closedRadialCollar k)).mono_set
        (p.radialCollar_subset_closedRadialCollar k)

omit [InnerProductSpace ℝ E] in
/-- Dimension zero has no exterior collar in
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem radialCollar_eq_empty_of_subsingleton [Subsingleton E] (k : ℕ) :
    p.radialCollar k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have : x = p.center := Subsingleton.elim _ _
  have := p.radius_pos.trans hx.1
  simp [‹x = p.center›] at this

end JanetCartan.BallExtension.Parameters
