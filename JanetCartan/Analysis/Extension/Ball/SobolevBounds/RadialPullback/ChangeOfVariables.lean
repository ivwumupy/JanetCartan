module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.RadialPullback.Geometry
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Change of variables on a radial collar

The analytic reduction of `app:ch_regular_base:eq:extension-collar-l2` to a
pointwise lower bound for the Jacobian. The Jacobian bound itself is a separate
proof obligation; these lemmas do not assert the final uniform estimate.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.BallExtension.Parameters

variable {n : ℕ} (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- The derivative used in the radial change of variables for
`app:ch_regular_base:eq:extension-collar-l2` exists everywhere in the collar. -/
theorem hasFDerivWithinAt_radialPoint_radialCollar (k : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ p.radialCollar k) :
    HasFDerivWithinAt (p.radialPoint k) (fderiv ℝ (p.radialPoint k) x)
      (p.radialCollar k) x :=
  ((p.contDiffAt_radialPoint k (p.ne_center_of_mem_closedRadialCollar
    (p.radialCollar_subset_closedRadialCollar k hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt

/-- Exact change of variables, with the actual derivative determinant, for
`app:ch_regular_base:eq:extension-collar-l2`. -/
theorem integral_image_radialCollar (k : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ y in p.radialPoint k '' p.radialCollar k, g y) =
      ∫ x in p.radialCollar k,
        |(fderiv ℝ (p.radialPoint k) x).det| * g (p.radialPoint k x) := by
  exact integral_image_eq_integral_abs_det_fderiv_smul volume
    (p.isOpen_radialCollar k).measurableSet
    (fun _ hx ↦ p.hasFDerivWithinAt_radialPoint_radialCollar k hx)
    (p.injOn_radialPoint_radialCollar k) g

/-- The analytic implication from a pointwise Jacobian lower bound to the
collar estimate in `app:ch_regular_base:eq:extension-collar-l2`. The remaining
geometric task is to prove the lower bound with `C = 2^k / 3^(n-1)`. -/
theorem mul_integral_comp_radialPoint_le_of_det_lower_bound
    (k : ℕ) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g (closedBall p.center p.radius))
    (hg0 : ∀ x ∈ closedBall p.center p.radius, 0 ≤ g x)
    {C : ℝ} (hdet : ∀ x ∈ p.radialCollar k,
      C ≤ |(fderiv ℝ (p.radialPoint k) x).det|) :
    C * (∫ x in p.radialCollar k, g (p.radialPoint k x)) ≤
      ∫ x in ball p.center p.radius, g x := by
  have hgi := hg.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)
  have hsub := p.radialPoint_image_radialCollar_subset_ball k
  have hj : IntegrableOn (fun x ↦ |(fderiv ℝ (p.radialPoint k) x).det| *
      g (p.radialPoint k x)) (p.radialCollar k) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (p.isOpen_radialCollar k).measurableSet
      (fun _ hx ↦ p.hasFDerivWithinAt_radialPoint_radialCollar k hx)
      (p.injOn_radialPoint_radialCollar k) g).mp
        (hgi.mono_set (hsub.trans ball_subset_closedBall))
  calc
    _ = ∫ x in p.radialCollar k, C * g (p.radialPoint k x) :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ x in p.radialCollar k,
        |(fderiv ℝ (p.radialPoint k) x).det| * g (p.radialPoint k x) := by
      apply integral_mono_ae
        ((p.integrableOn_comp_radialPoint_radialCollar hg k).const_mul C) hj
      filter_upwards [ae_restrict_mem (p.isOpen_radialCollar k).measurableSet] with x hx
      exact mul_le_mul_of_nonneg_right (hdet x hx)
        (hg0 _ (ball_subset_closedBall (p.radialPoint_mem_ball_of_scaled_lt hx.1 hx.2)))
    _ = ∫ y in p.radialPoint k '' p.radialCollar k, g y :=
      (p.integral_image_radialCollar k g).symm
    _ ≤ _ := by
      apply setIntegral_mono_set (hgi.mono_set ball_subset_closedBall)
      · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact hg0 x (ball_subset_closedBall hx)
      · exact Filter.Eventually.of_forall hsub

end JanetCartan.BallExtension.Parameters
