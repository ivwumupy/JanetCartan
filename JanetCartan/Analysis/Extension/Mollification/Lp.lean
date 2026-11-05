module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Translation and normalized smoothing in Lᵖ

Ingredients for the Sobolev density argument in Appendix B,
`app:ch_regular_base:lem:ball-extension` of `paper.tex`. Translation continuity
holds for every finite p ≥ 1. Averaging over the normalized bump probability
measure gives an L² contraction and L² convergence of the actual convolution.
These results apply to arbitrary L² data; no weak-derivative statement is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set ContinuousLinearMap
open scoped ENNReal Topology Convolution

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ F] in
/-- Appendix B, ball-extension density: translation is continuous in Lᵖ for
`1 ≤ p < ∞`, without any classical regularity assumption on the input. -/
theorem continuous_translateLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp F p μ) :
    Continuous (fun y : E ↦ Lp.compMeasurePreserving (fun x : E ↦ x - y)
      (measurePreserving_sub_right μ y) f) := by
  let T : C(E, C(E, E)) := (⟨fun z : E × E ↦ z.2 - z.1,
    continuous_snd.sub continuous_fst⟩ : C(E × E, E)).curry
  exact continuous_const.compMeasurePreservingLp T.continuous _ hp

/-- Appendix B, ball-extension density: the normalized bump defines a probability
measure used to average translations. -/
def bumpMeasure (φ : ContDiffBump (0 : E)) : Measure E :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (φ.normed μ x))

instance isProbabilityMeasure_bumpMeasure (φ : ContDiffBump (0 : E)) :
    IsProbabilityMeasure (bumpMeasure μ φ) where
  measure_univ := by
    rw [bumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (.of_forall φ.nonneg_normed), φ.integral_normed]
    simp

omit [μ.IsAddHaarMeasure] in
/-- Appendix B, ball-extension density: the averaging measure has exactly the
usual normalized-convolution integral. -/
theorem integral_bumpMeasure (φ : ContDiffBump (0 : E)) (f : E → F) :
    ∫ y, f y ∂bumpMeasure μ φ = ∫ y, φ.normed μ y • f y ∂μ := by
  rw [bumpMeasure, integral_withDensity_eq_integral_toReal_smul
    ((φ.contDiff_normed (n := 0)).continuous.measurable.ennreal_ofReal)
    (.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _)]

omit [NormedSpace ℝ F] in
/-- Appendix B, ball-extension density: squared L² norm as a nonnegative integral. -/
theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → F}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Appendix B, ball-extension density: averaging over a probability measure
bounds the squared norm by the average of squared norms. -/
theorem enorm_integral_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → F} (hf : AEStronglyMeasurable f ν) :
    ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [← eLpNorm_two_sq hf]
  apply pow_le_pow_left' _ 2
  calc
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 ν := (eLpNorm_one_eq_lintegral_enorm hf).symm
    _ ≤ eLpNorm f 2 ν := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

omit [NormedSpace ℝ F] in
/-- Appendix B, ball-extension density: the Lᵖ norm of the translation error
tends to zero for every Lᵖ function, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_translate_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp F p μ) :
    Tendsto (fun y : E ↦ eLpNorm (fun x ↦ f (x - y) - f x) p μ) (𝓝 0) (𝓝 0) := by
  have h := ((continuous_translateLp μ hp f).sub (continuous_const (y := f))).enorm.tendsto (0 : E)
  have hz : Lp.compMeasurePreserving (fun x : E ↦ x - 0)
      (measurePreserving_sub_right μ 0) f = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right μ 0)]
      with x hx
    simpa using hx
  simp only [Pi.sub_apply] at h
  rw [hz, sub_self, enorm_zero] at h
  convert h using 1
  ext y
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (fun x : E ↦ x - y)
    (measurePreserving_sub_right μ y) f) f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right μ y)] with x hx hx'
  exact (hx.trans (congrArg (fun z ↦ z - f x) hx')).symm

/-- Appendix B, ball-extension density: the averaging measure is concentrated
inside the support radius of its bump. -/
theorem ae_mem_ball_bumpMeasure (φ : ContDiffBump (0 : E)) :
    ∀ᵐ y ∂bumpMeasure μ φ, y ∈ Metric.ball (0 : E) φ.rOut := by
  rw [bumpMeasure, ae_withDensity_iff
    ((φ.contDiff_normed (n := 0)).continuous.measurable.ennreal_ofReal)]
  filter_upwards with y hy
  rw [← φ.support_normed_eq (μ := μ)]
  exact fun h ↦ hy (by simp [h])

/-- Appendix B, ball-extension density: translations of L² data are integrable
against the compactly supported averaging measure. -/
theorem integrable_translate_bumpMeasure (φ : ContDiffBump (0 : E))
    (f : Lp F 2 μ) (x : E) :
    Integrable (fun y ↦ f (x - y)) (bumpMeasure μ φ) := by
  rw [bumpMeasure, integrable_withDensity_iff_integrable_smul'
    ((φ.contDiff_normed (n := 0)).continuous.measurable.ennreal_ofReal)
    (.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _)]
  exact (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (L := lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous
    ((Lp.memLp f).locallyIntegrable (by norm_num)) x

variable [CompleteSpace F]

/-- Appendix B, ball-extension density: the squared L² smoothing error is bounded
by the bump average of the squared L² translation errors, for arbitrary L² data. -/
theorem eLpNorm_two_convolution_sub_sq_le (φ : ContDiffBump (0 : E)) (f : Lp F 2 μ) :
    eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F) - (f : E → F)) 2 μ ^ 2 ≤
      ∫⁻ y, eLpNorm (fun x ↦ f (x - y) - f x) 2 μ ^ 2 ∂bumpMeasure μ φ := by
  have hc := (φ.hasCompactSupport_normed (μ := μ)).continuous_convolution_left
    (L := lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous
    ((Lp.memLp f).locallyIntegrable (by norm_num))
  rw [eLpNorm_two_sq (hc.aestronglyMeasurable.sub (Lp.aestronglyMeasurable f))]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖f (x - y) - f x‖ₑ ^ 2 ∂bumpMeasure μ φ ∂μ := by
      apply lintegral_mono
      intro x
      have heq : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F)) x - f x =
          ∫ y, f (x - y) - f x ∂bumpMeasure μ φ := by
        rw [integral_sub (integrable_translate_bumpMeasure μ φ f x) (integrable_const _),
          integral_bumpMeasure, integral_const]
        simp [convolution, measureReal_def]
      simp only [Pi.sub_apply, heq]
      exact enorm_integral_sq_le
        (((Lp.stronglyMeasurable f).comp_measurable (measurable_const.sub measurable_id)).sub
          stronglyMeasurable_const).aestronglyMeasurable
    _ = ∫⁻ y, ∫⁻ x, ‖f (x - y) - f x‖ₑ ^ 2 ∂μ ∂bumpMeasure μ φ := by
      apply lintegral_lintegral_swap
      exact ((((Lp.stronglyMeasurable f).comp_measurable (measurable_fst.sub measurable_snd)).sub
        ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)).enorm.pow_const 2).aemeasurable
    _ = _ := by
      congr 1
      funext y
      exact (eLpNorm_two_sq
        (((Lp.stronglyMeasurable f).comp_measurable (measurable_id.sub measurable_const)).sub
          (Lp.stronglyMeasurable f)).aestronglyMeasurable).symm

/-- Appendix B, ball-extension density: shrinking normalized bumps converge in
L² for arbitrary L² data, with no support or smoothness hypothesis. -/
theorem tendsto_eLpNorm_two_convolution_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (f : Lp F 2 μ) :
    Tendsto (fun i ↦ eLpNorm
      ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F) - (f : E → F)) 2 μ) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have ht := ENNReal.Tendsto.pow (n := 2)
    (tendsto_eLpNorm_translate_sub μ (p := 2) (by norm_num) f)
  simp only [zero_pow (by decide : 2 ≠ 0)] at ht
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp
    (ht.eventually (gt_mem_nhds (bot_lt_iff_ne_bot.mpr (pow_ne_zero 2 hε.ne'))))
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with i hi
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.rpow_natCast, ENNReal.rpow_natCast]
  calc
    _ ≤ ∫⁻ y, eLpNorm (fun x ↦ f (x - y) - f x) 2 μ ^ 2 ∂bumpMeasure μ (φ i) :=
      eLpNorm_two_convolution_sub_sq_le μ (φ i) f
    _ ≤ ∫⁻ _y : E, ε ^ 2 ∂bumpMeasure μ (φ i) := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_ball_bumpMeasure μ (φ i)] with y hy
      exact (hd (lt_trans hy hi)).le
    _ = ε ^ 2 := by simp

omit [CompleteSpace F] in
/-- Appendix B, ball-extension density: normalized convolution is a contraction
in L². The constant is one and is independent of the support radius. -/
theorem eLpNorm_two_convolution_le (φ : ContDiffBump (0 : E)) (f : Lp F 2 μ) :
    eLpNorm (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F)) 2 μ ≤ eLpNorm f 2 μ := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.rpow_natCast, ENNReal.rpow_natCast]
  have hc := (φ.hasCompactSupport_normed (μ := μ)).continuous_convolution_left
    (L := lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous
    ((Lp.memLp f).locallyIntegrable (by norm_num))
  rw [eLpNorm_two_sq hc.aestronglyMeasurable, eLpNorm_two_sq (Lp.aestronglyMeasurable f)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖f (x - y)‖ₑ ^ 2 ∂bumpMeasure μ φ ∂μ := by
      apply lintegral_mono
      intro x
      have heq : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F)) x =
          ∫ y, f (x - y) ∂bumpMeasure μ φ := by
        rw [integral_bumpMeasure]
        rfl
      simp only [heq]
      exact enorm_integral_sq_le
        ((Lp.stronglyMeasurable f).comp_measurable
          (measurable_const.sub measurable_id)).aestronglyMeasurable
    _ = ∫⁻ y, ∫⁻ x, ‖f (x - y)‖ₑ ^ 2 ∂μ ∂bumpMeasure μ φ := by
      apply lintegral_lintegral_swap
      exact (((Lp.stronglyMeasurable f).comp_measurable
        (measurable_fst.sub measurable_snd)).enorm.pow_const 2).aemeasurable
    _ = _ := by
      simp_rw [lintegral_sub_right_eq_self (fun x ↦ ‖f x‖ₑ ^ 2)]
      simp

end JanetCartan.Mollification
