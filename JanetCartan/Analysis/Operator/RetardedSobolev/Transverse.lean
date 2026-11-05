module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Transverse differentiation of retarded primitives

The transverse derivative passes under the integral in the proof of
`app:ch_osc:prop:osc-retarded-tube` in `paper.tex`. A compact time interval and a
compact parameter neighborhood supply domination from joint continuity of the
derivative. Both orders of the time endpoints are allowed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace JanetCartan.RetardedSobolev

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ProperSpace Y]

/-- Transverse differentiation under the finite time integral, used for both signed
primitives in `app:ch_osc:prop:osc-retarded-tube`. The integrable dominating bound is
proved from continuity on a compact neighborhood, rather than assumed. -/
theorem hasFDerivAt_intervalIntegral_parameter
    {g : Y → ℝ → E} {g' : Y → ℝ → Y →L[ℝ] E}
    (hg : Continuous (Function.uncurry g)) (hg' : Continuous (Function.uncurry g'))
    (hd : ∀ y s, HasFDerivAt (fun z ↦ g z s) (g' y s) y) (a b : ℝ) (y : Y) :
    HasFDerivAt (fun z ↦ ∫ s in a..b, g z s) (∫ s in a..b, g' y s) y := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hg'.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall y 1) (bound := fun _ ↦ C)
    (Metric.closedBall_mem_nhds y (by norm_num))
  · exact Filter.Eventually.of_forall (fun z ↦
      (hg.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hg'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun s hs z hz ↦
      hC (z, s) ⟨hz, uIoc_subset_uIcc hs⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun s _ z _ ↦ hd z s)

/-- The `C¹` form of transverse commutation in
`app:ch_osc:prop:osc-retarded-tube`, with the parameter derivative written as the
restriction of the full Fréchet derivative to transverse directions. -/
theorem hasFDerivAt_intervalIntegral_parameter_of_contDiff
    {g : Y × ℝ → E} (hg : ContDiff ℝ 1 g) (a b : ℝ) (y : Y) :
    HasFDerivAt (fun z ↦ ∫ s in a..b, g (z, s))
      (∫ s in a..b, (fderiv ℝ g (y, s)).comp (ContinuousLinearMap.inl ℝ Y ℝ)) y := by
  apply hasFDerivAt_intervalIntegral_parameter
    (g := fun z s ↦ g (z, s))
    (g' := fun z s ↦ (fderiv ℝ g (z, s)).comp (ContinuousLinearMap.inl ℝ Y ℝ)) hg.continuous
    ((hg.continuous_fderiv (by norm_num)).clm_comp continuous_const)
  intro z s
  exact ((hg.differentiable (by norm_num)) (z, s)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_left z s)

end JanetCartan.RetardedSobolev
