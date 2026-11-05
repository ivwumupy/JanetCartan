module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.Integrability
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Positive-time regularity of spatial heat jets

The derivative integrands in `app:ch_background:prop:bg-frame`, Step 1,
are measurable in time because they are jointly smooth at positive times.
This supplies the measurability premise of dominated differentiation;
no bound on an integrated kernel derivative is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Joint smoothness of the explicit integrand at positive times
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem contDiffOn_imageBesselKernel_integrand :
    ContDiffOn ℝ ∞ (fun p : E × ℝ ↦
      p.2 ^ (-(1 : ℝ) / 2) * Real.exp (-p.2) * imageBesselHeatKernel p.2 p.1)
      (univ ×ˢ Ioi 0) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have ht : p.2 ≠ 0 := ne_of_gt hp.2
  have hb : 4 * Real.pi * p.2 ≠ 0 := mul_ne_zero (by positivity) ht
  unfold imageBesselHeatKernel
  have hn : ContDiffAt ℝ ∞ (fun q : E × ℝ ↦ ‖q.1‖ ^ 2) p :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffAt
  fun_prop (disch := aesop)

/-- Joint smoothness of every spatial jet of the positive-time integrand,
used to justify the integral differentiation in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem contDiffOn_imageBesselKernel_integrand_jet (n : ℕ) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ ↦ iteratedFDeriv ℝ n
      (fun x : E ↦ p.2 ^ (-(1 : ℝ) / 2) * Real.exp (-p.2) *
        imageBesselHeatKernel p.2 x) p.1) (univ ×ˢ Ioi 0) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.contDiff.comp_contDiffOn
        (contDiffOn_imageBesselKernel_integrand (d := d))
  | succ n ih =>
    have hd := JanetCartan.contDiffOn_parameterFDeriv isOpen_univ isOpen_Ioi ih
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).symm.contDiff
        |>.comp_contDiffOn hd

/-- Time measurability of the actual spatial derivative integrands
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem aestronglyMeasurable_imageBesselKernel_integrand_jet (n : ℕ) (x : E) :
    AEStronglyMeasurable (fun t : ℝ ↦ iteratedFDeriv ℝ n
      (fun y : E ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t y) x)
      (volume.restrict (Ioi 0)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  exact (contDiffOn_imageBesselKernel_integrand_jet n).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨mem_univ _, ht⟩)

end JanetCartan.ContinuumNormalReduction.ImageNormal
