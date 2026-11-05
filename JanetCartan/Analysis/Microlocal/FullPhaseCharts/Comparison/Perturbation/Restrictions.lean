module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Uniform
public import Mathlib.Analysis.Normed.Operator.Prod

/-! # Contractive restrictions of the joint chart derivative

These elementary chain-rule estimates transfer the joint comparison of
`app:ch_seed:prop:seed-phase-charts` to its data and transverse restrictions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.FullPhaseCharts.Comparison

/-- Restricting the input and projecting the output by contractions preserves
the derivative error bound in `app:ch_seed:prop:seed-phase-charts`. Used for the
full coordinates, the `(z,η)` data slice, and the transverse direction slice. -/
theorem norm_fderiv_chart_restriction_sub_le
    {A Q X F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Q → X} {ι : A → Q} {a : A}
    (hf : DifferentiableAt ℝ f (ι a)) (hg : DifferentiableAt ℝ g (ι a))
    (hi : DifferentiableAt ℝ ι a) (hni : ‖fderiv ℝ ι a‖ ≤ 1)
    (L : X →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    ‖fderiv ℝ (fun b ↦ L (f (ι b))) a - fderiv ℝ (fun b ↦ L (g (ι b))) a‖ ≤
      ‖fderiv ℝ f (ι a) - fderiv ℝ g (ι a)‖ := by
  have hf' := (L.hasFDerivAt.comp a (hf.hasFDerivAt.comp a hi.hasFDerivAt)).fderiv
  have hg' := (L.hasFDerivAt.comp a (hg.hasFDerivAt.comp a hi.hasFDerivAt)).fderiv
  simp only [Function.comp_def] at hf' hg'
  rw [hf', hg',
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact (L.opNorm_comp_le _).trans ((mul_le_mul hL
    (((fderiv ℝ f (ι a) - fderiv ℝ g (ι a)).opNorm_comp_le _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hni)) (norm_nonneg _) zero_le_one).trans
        (by simp))

/-- The product coordinates of the Euclidean full chart are a contraction,
as used in `app:ch_seed:prop:seed-phase-charts`. -/
theorem norm_fullChart_coordinates_le_one
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap‖ ≤ 1 := by
  refine (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap.opNorm_le_bound
    zero_le_one ?_
  intro x
  change ‖x.ofLp‖ ≤ 1 * ‖x‖
  rw [one_mul, Prod.norm_def]
  exact max_le (WithLp.norm_fst_le ℝ x) (WithLp.norm_snd_le ℝ x)

end JanetCartan.FullPhaseCharts.Comparison
