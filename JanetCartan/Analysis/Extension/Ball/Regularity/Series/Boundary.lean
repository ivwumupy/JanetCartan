module

public import JanetCartan.Analysis.Extension.Ball.Regularity.Jets
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Geometry.Euclidean.Inversion.Calculus

/-!
# Extending exterior derivatives to the sphere

The boundary argument following `app:ch_regular_base:eq:extension-collar-l2`.
Inversion reduces the closed exterior to a punctured closed ball, where convexity
allows a continuous limiting derivative to extend from the interior.
-/

@[expose] public noncomputable section

open Set Metric Filter EuclideanGeometry
open scoped Topology ContDiff

namespace JanetCartan.BallExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local convex boundary extension, used after
`app:ch_regular_base:eq:extension-collar-l2`. Removing the center permits inversion. -/
theorem hasFDerivWithinAt_puncturedClosedBall {c x : E} {R : ℝ} (hR : 0 < R)
    {f : E → F} {g : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closedBall c R \ {c}))
    (hg : ContinuousOn g (closedBall c R \ {c}))
    (hd : ∀ y ∈ ball c R \ {c}, HasFDerivAt f (g y) y)
    (hx : x ∈ closedBall c R \ {c}) :
    HasFDerivWithinAt f (g x) (closedBall c R \ {c}) x := by
  have hxc : x ≠ c := hx.2
  let r := dist x c / 2
  have hr : 0 < r := half_pos (dist_pos.mpr hxc)
  let s := ball c R ∩ ball x r
  have hs : IsOpen s := isOpen_ball.inter isOpen_ball
  have hsub : closure s ⊆ closedBall c R \ {c} := by
    intro y hy
    have hyc : y ∈ closedBall c R := by
      simpa [closure_ball _ hR.ne'] using closure_mono inter_subset_left hy
    have hyx : y ∈ closedBall x r := by
      simpa only [closure_closedBall] using
        closure_mono (inter_subset_right.trans ball_subset_closedBall) hy
    refine ⟨hyc, ?_⟩
    intro heq
    have hyx' := mem_closedBall.mp hyx
    have : y = c := heq
    rw [this, dist_comm] at hyx'
    dsimp [r] at hyx'
    linarith [dist_pos.mpr hxc]
  have hsmall : closure s ∈ 𝓝[closedBall c R \ {c}] x := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
      self_mem_nhdsWithin] with y hy hyc
    have hy' : y ∈ ball x r ∩ closure (ball c R) :=
      ⟨hy, by simpa [closure_ball _ hR.ne'] using hyc.1⟩
    simpa only [s, inter_comm] using isOpen_ball.inter_closure hy'
  have hder : ∀ y ∈ s, HasFDerivAt f (g y) y := by
    intro y hy
    exact hd y ⟨hy.1, (hsub (subset_closure hy)).2⟩
  apply HasFDerivWithinAt.mono_of_mem_nhdsWithin (t := closure s) _ hsmall
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (hder y hy).differentiableAt.differentiableWithinAt)
    ((convex_ball c R).inter (convex_ball x r)) hs
    (fun y hy ↦ (hf y (hsub hy)).mono (subset_closure.trans hsub))
  apply ((hg x hx).mono (subset_closure.trans hsub)).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hder y hy).fderiv.symm

namespace Parameters

variable (p : Parameters E)

/-- A continuous exterior derivative extends to the sphere. This is the geometric
step in the uniform derivative argument after
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem hasFDerivWithinAt_closedExterior {f : E → F} {g : E → E →L[ℝ] F}
    (hf : ContinuousOn f {y | p.radius ≤ ‖y - p.center‖})
    (hg : ContinuousOn g {y | p.radius ≤ ‖y - p.center‖})
    (hd : ∀ y, p.radius < ‖y - p.center‖ → HasFDerivAt f (g y) y)
    {x : E} (hx : p.radius ≤ ‖x - p.center‖) :
    HasFDerivWithinAt f (g x) {y | p.radius ≤ ‖y - p.center‖} x := by
  let I := inversion p.center p.radius
  let D := fderiv ℝ I
  let B := closedBall p.center p.radius \ {p.center}
  let X := {y : E | p.radius ≤ ‖y - p.center‖}
  have hi (y : E) : I (I y) = y := inversion_inversion _ p.radius_pos.ne' y
  have hne {y : E} (hy : y ∈ X) : y ≠ p.center := by
    intro heq
    have : p.radius ≤ 0 := by simpa [X, heq] using hy
    exact p.radius_pos.not_ge this
  have hIB : MapsTo I B X := by
    intro y hy
    change p.radius ≤ ‖I y - p.center‖
    rw [← dist_eq_norm, dist_inversion_center]
    apply (le_div_iff₀ (dist_pos.mpr hy.2)).mpr
    nlinarith [mem_closedBall.mp hy.1, p.radius_pos]
  have hIX : MapsTo I X B := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_inversion_center]
      apply (div_le_iff₀ (dist_pos.mpr (hne hy))).mpr
      have := hy
      change p.radius ≤ ‖y - p.center‖ at this
      rw [← dist_eq_norm] at this
      nlinarith [p.radius_pos]
    · exact (inversion_eq_center p.radius_pos.ne').not.mpr (hne hy)
  have hIsmooth {y : E} (hy : y ≠ p.center) : ContDiffAt ℝ ∞ I y :=
    contDiffAt_const.inversion contDiffAt_const contDiffAt_id hy
  have hId {y : E} (hy : y ≠ p.center) : HasFDerivAt I (D y) y :=
    ((hIsmooth hy).differentiableAt (by simp)).hasFDerivAt
  have hIc : ContinuousOn I B := fun y hy ↦ (hId hy.2).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D B := fun y hy ↦
    ((hIsmooth hy.2).continuousAt_fderiv (by simp)).continuousWithinAt
  have hfc : ContinuousOn (fun y ↦ f (I y)) B := hf.comp hIc hIB
  have hgc : ContinuousOn (fun y ↦ (g (I y)).comp (D y)) B :=
    (hg.comp hIc hIB).clm_comp hDc
  have hdI : ∀ y ∈ ball p.center p.radius \ {p.center},
      HasFDerivAt (fun z ↦ f (I z)) ((g (I y)).comp (D y)) y := by
    intro y hy
    apply (hd (I y) ?_).comp y (hId hy.2)
    rw [← dist_eq_norm, dist_inversion_center]
    apply (lt_div_iff₀ (dist_pos.mpr hy.2)).mpr
    nlinarith [mem_ball.mp hy.1, p.radius_pos]
  have hext := hasFDerivWithinAt_puncturedClosedBall p.radius_pos hfc hgc hdI (hIX hx)
  have hcomp := hext.comp x (hId (hne hx)).hasFDerivWithinAt hIX
  have hDi : (D (I x)).comp (D x) = ContinuousLinearMap.id ℝ E := by
    have hh := (hId ((inversion_eq_center p.radius_pos.ne').not.mpr (hne hx))).comp x
      (hId (hne hx))
    change HasFDerivAt (I ∘ I) ((D (I x)).comp (D x)) x at hh
    have hh' : HasFDerivAt (fun y : E ↦ y) ((D (I x)).comp (D x)) x := by
      simpa only [Function.comp_def, hi] using hh
    exact hh'.unique (hasFDerivAt_id x)
  simpa only [Function.comp_def, hi, ContinuousLinearMap.comp_assoc, hDi,
    ContinuousLinearMap.comp_id] using hcomp

end Parameters

end JanetCartan.BallExtension
