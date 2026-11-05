module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local flows with a prescribed range

The flow construction in `app:lem:common-hamilton-phase` needs a common time interval
and a spatial buffer. We retain the range information from Picard iteration, which
is not part of Mathlib's public local-flow existence statement. These results prove
continuous and Lipschitz dependence only; differentiable dependence is a separate step.
-/

@[expose] public section

open Function Metric Set
open scoped Topology NNReal

namespace JanetCartan.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `app:lem:common-hamilton-phase`: Picard–Lindelöf with the range bound retained.
The same flow has a uniform Lipschitz constant in its initial point. -/
theorem exists_localFlow_with_range
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ Φ : E × ℝ → E,
      (∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun s ↦ Φ (x, s)) (f t (Φ (x, t))) (Icc tmin tmax) t) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax, Φ (x, t) ∈ closedBall x₀ a) ∧
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc tmin tmax) ∧
      ∃ K' : ℝ≥0, ∀ t ∈ Icc tmin tmax,
        LipschitzOnWith K' (fun x ↦ Φ (x, t)) (closedBall x₀ r) := by
  classical
  have hex (x) (hx : x ∈ closedBall x₀ r) :=
    _root_.ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hex
  let Φ : E × ℝ → E := fun z ↦
    if hx : z.1 ∈ closedBall x₀ r then (α z.1 hx).compProj z.2 else 0
  have hΦ (x) (hx : x ∈ closedBall x₀ r) (t : ℝ) :
      Φ (x, t) = (α x hx).compProj t := by dsimp only [Φ]; rw [dite_eq_left hx]
  have hinit (x) (hx : x ∈ closedBall x₀ r) : Φ (x, t₀) = x := by
    rw [hΦ x hx, _root_.ODE.FunSpace.compProj_val, ← hα,
      _root_.ODE.FunSpace.next_apply₀]
  have hderiv (x) (hx : x ∈ closedBall x₀ r) (t) (ht : t ∈ Icc tmin tmax) :
      HasDerivWithinAt (fun s ↦ Φ (x, s)) (f t (Φ (x, t))) (Icc tmin tmax) t := by
    simp_rw [hΦ x hx]
    apply _root_.ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx).continuous_compProj.continuousOn
      (fun _ _ ↦ (α x hx).compProj_mem_closedBall hf.mul_max_le) x ht
      |>.congr_of_mem _ ht
    intro s hs
    nth_rw 1 [← hα]
    rw [_root_.ODE.FunSpace.compProj_of_mem hs, _root_.ODE.FunSpace.next_apply]
  obtain ⟨K', hK'⟩ := _root_.ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hlip (t) (ht : t ∈ Icc tmin tmax) :
      LipschitzOnWith K' (fun x ↦ Φ (x, t)) (closedBall x₀ r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hΦ x hx, hΦ y hy, _root_.ODE.FunSpace.compProj_of_mem ht,
      _root_.ODE.FunSpace.compProj_of_mem ht]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    exact ContinuousMap.dist_le_iff_of_nonempty.mp
      (hK' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)) ⟨t, ht⟩
  refine ⟨Φ, hinit, hderiv, ?_, ?_, K', hlip⟩
  · intro x hx t _
    rw [hΦ x hx]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  · exact continuousOn_prod_of_continuousOn_lipschitzOnWith Φ K'
      (fun x hx ↦ HasDerivWithinAt.continuousOn (hderiv x hx)) hlip

/-- `app:lem:common-hamilton-phase`: a `C¹` field admits a common local flow in any
prescribed open neighborhood of the base point. Both the initial ball and the time
interval have positive radius; their interiors give a bounded open flow domain.
All trajectories on the closed time interval stay in the prescribed neighborhood. -/
theorem exists_localFlow_in_open
    {f : E → E} {x₀ : E} {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E × ℝ → E,
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) ∧
      (∀ x ∈ closedBall x₀ r, Φ (x, t₀) = x) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt (fun s ↦ Φ (x, s)) (f (Φ (x, t))) t) ∧
      (∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), Φ (x, t) ∈ U) ∧
      ∃ K : ℝ≥0, ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        LipschitzOnWith K (fun x ↦ Φ (x, t)) (closedBall x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  have hra : (r : ℝ) ≤ a := by
    have h := (hpl t₀).mul_max_le
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self] at h
    have : 0 ≤ (L : ℝ) * ε := mul_nonneg L.coe_nonneg hε.le
    linarith
  have ha : (0 : ℝ) < a := lt_of_lt_of_le (by exact_mod_cast hr) hra
  let b : ℝ≥0 := ⟨min (a : ℝ) (δ / 2), le_of_lt (lt_min ha (half_pos hδ))⟩
  have hb : 0 < b := by change 0 < min (a : ℝ) (δ / 2); positivity
  have hba : b ≤ a := by exact min_le_left _ _
  obtain ⟨η, hη, hsmall⟩ := (hpl t₀).exists_shrink_radius hε hba (half_lt_self hb)
  obtain ⟨Φ, hinit, hderiv, hrange, hcont, K', hlip⟩ := exists_localFlow_with_range hsmall
  refine ⟨(b / 2 : ℝ≥0), by exact_mod_cast half_pos hb, η, hη, Φ, hcont,
    hinit, ?_, ?_, K', hlip⟩
  · intro x hx t ht
    exact (hderiv x hx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro x hx t ht
    apply hδU
    exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)))
      (hrange x hx t ht)

end JanetCartan.ODE
