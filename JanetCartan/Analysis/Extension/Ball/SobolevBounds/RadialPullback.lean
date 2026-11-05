module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.RadialPullback.ChangeOfVariables
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.RadialPullback.Jacobian

/-!
# Radial collar pullbacks

The quantitative change-of-variables estimate underlying
`app:ch_regular_base:eq:extension-collar-l2`. Pulling back a continuous nonnegative
function to the `k`th radial collar costs at most `3 ^ (n - 1) / 2 ^ k` in its
integral. The constant is uniform in the sampling index and the input function.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace JanetCartan.BallExtension.Parameters

/-- In dimension zero the collar estimate of
`app:ch_regular_base:eq:extension-collar-l2` holds because the exterior is empty. -/
theorem exists_radialCollar_integral_bound_dim_zero
    (p : Parameters (EuclideanSpace ℝ (Fin 0))) :
    ∃ D : ℝ, 0 < D ∧ ∀ (k : ℕ) (g : EuclideanSpace ℝ (Fin 0) → ℝ),
      ContinuousOn g (closedBall p.center p.radius) →
      (∀ x ∈ closedBall p.center p.radius, 0 ≤ g x) →
      IntegrableOn (g ∘ p.radialPoint k) (p.radialCollar k) ∧
      (∫ x in p.radialCollar k, g (p.radialPoint k x)) ≤
        (D / (2 : ℝ) ^ k) * ∫ x in ball p.center p.radius, g x := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro k g _ hg0
  rw [p.radialCollar_eq_empty_of_subsingleton]
  refine ⟨integrableOn_empty, ?_⟩
  rw [setIntegral_empty]
  exact mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_ball (fun x hx ↦ hg0 x (ball_subset_closedBall hx)))

/-- The radial change-of-variables estimate behind
`app:ch_regular_base:eq:extension-collar-l2`, with the explicit dimension-dependent
constant `3 ^ (n - 1)`. The determinant lower bound is proved by the radial and
tangential derivative calculation; dimension zero has an empty collar. -/
theorem integral_comp_radialPoint_le {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g (closedBall p.center p.radius))
    (hg0 : ∀ x ∈ closedBall p.center p.radius, 0 ≤ g x) :
    (∫ x in p.radialCollar k, g (p.radialPoint k x)) ≤
      ((3 : ℝ) ^ (n - 1) / (2 : ℝ) ^ k) * ∫ x in ball p.center p.radius, g x := by
  by_cases hn : n = 0
  · subst n
    rw [p.radialCollar_eq_empty_of_subsingleton, setIntegral_empty]
    exact mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_ball
        (fun x hx ↦ hg0 x (ball_subset_closedBall hx)))
  · have hbound := p.mul_integral_comp_radialPoint_le_of_det_lower_bound k hg hg0
      (fun _ hx ↦ p.radialCollar_jacobian_lower_bound (Nat.pos_of_ne_zero hn) k hx)
    calc
      _ ≤ (∫ x in ball p.center p.radius, g x) /
          ((2 : ℝ) ^ k / (3 : ℝ) ^ (n - 1)) :=
        (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hbound)
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring

/-- In dimension one the radial substitution in
`app:ch_regular_base:eq:extension-collar-l2` has exactly the factor `2 ^ (-k)`;
there is no tangential Jacobian loss. -/
theorem integral_comp_radialPoint_le_dim_one
    (p : Parameters (EuclideanSpace ℝ (Fin 1))) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hg : ContinuousOn g (closedBall p.center p.radius))
    (hg0 : ∀ x ∈ closedBall p.center p.radius, 0 ≤ g x) :
    (∫ x in p.radialCollar k, g (p.radialPoint k x)) ≤
      (1 / (2 : ℝ) ^ k) * ∫ x in ball p.center p.radius, g x := by
  simpa using p.integral_comp_radialPoint_le k hg hg0

/-- Uniform integrability and quantitative radial pullback bound for
`app:ch_regular_base:eq:extension-collar-l2`. The positive constant can be chosen
as `3 ^ (n - 1)`, independently of `k` and `g`, in every dimension. -/
theorem exists_radialCollar_integral_bound {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n))) :
    ∃ D : ℝ, 0 < D ∧ ∀ (k : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContinuousOn g (closedBall p.center p.radius) →
      (∀ x ∈ closedBall p.center p.radius, 0 ≤ g x) →
      IntegrableOn (g ∘ p.radialPoint k) (p.radialCollar k) ∧
      (∫ x in p.radialCollar k, g (p.radialPoint k x)) ≤
        (D / (2 : ℝ) ^ k) * ∫ x in ball p.center p.radius, g x := by
  refine ⟨(3 : ℝ) ^ (n - 1), by positivity, ?_⟩
  intro k g hg hg0
  exact ⟨p.integrableOn_comp_radialPoint_radialCollar hg k,
    p.integral_comp_radialPoint_le k hg hg0⟩

end JanetCartan.BallExtension.Parameters
