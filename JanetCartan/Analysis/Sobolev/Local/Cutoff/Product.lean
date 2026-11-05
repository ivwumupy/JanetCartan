module

public import JanetCartan.Analysis.Sobolev.Local.Scale.WeakJet
public import JanetCartan.Analysis.Operator.SmallSupport.Cutoff

/-!
# The weak product rule for cutoff multiplication

The first derivative used in `app:ch_regular:eq:one-gain-tame` is obtained
by testing the original weak derivative against the product of the cutoff
and the test function. No multiplier estimate is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- A bounded continuous scalar multiplier preserves L², as needed for the
cutoff in `app:ch_regular:thm:exact-correction`. -/
theorem memLp_bounded_smul {f : E → F} (hf : MemLp f 2 μ)
    {χ : E → ℝ} (hχ : Continuous χ) {B : ℝ} (hB : ∀ x, ‖χ x‖ ≤ B) :
    MemLp (fun x ↦ χ x • f x) 2 μ :=
  hf.of_le_mul (hχ.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

/-- L² control of the differentiated cutoff term in
`app:ch_regular:eq:one-gain-tame`. -/
theorem memLp_bounded_smulRight {f : E → F} (hf : MemLp f 2 μ)
    {D : E → E →L[ℝ] ℝ} (hD : Continuous D) {B : ℝ} (hB : ∀ x, ‖D x‖ ≤ B) :
    MemLp (fun x ↦ (D x).smulRight (f x)) 2 μ := by
  apply hf.of_le_mul
  · exact (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable
      (hD.aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
  · exact Eventually.of_forall fun x ↦ by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [NormedSpace ℝ F] in
/-- Passing a pointwise norm bound to the real L² norm, for the cutoff
constants in `app:ch_regular:eq:one-gain-tame`. -/
theorem eLpNorm_toReal_le_mul_of_bound
    {G : Type*} [NormedAddCommGroup G] {f : E → F} {g : E → G}
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    {B : ℝ} (hB : 0 ≤ B) (hfg : ∀ x, ‖f x‖ ≤ B * ‖g x‖) :
    (eLpNorm f 2 μ).toReal ≤ B * (eLpNorm g 2 μ).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf (Eventually.of_forall hfg) 2)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] using h

end JanetCartan.LocalSobolev

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The genuine weak product identity used for the cutoff in
`app:ch_regular:eq:one-gain-tame`. Only the original weak derivative and
bounds on the fixed smooth multiplier and its derivative are inputs. -/
theorem HasWeakFDerivOn.smooth_smul_univ
    {f : E → F} {D : E → E →L[ℝ] F}
    (hw : HasWeakFDerivOn μ f D univ) (hf : MemLp f 2 μ) (hD : MemLp D 2 μ)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {B₀ B₁ : ℝ} (hB₀ : ∀ x, ‖χ x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ B₁) :
    HasWeakFDerivOn μ (fun x ↦ χ x • f x)
      (fun x ↦ (fderiv ℝ χ x).smulRight (f x) + χ x • D x) univ := by
  have hχD := hχ.continuous_fderiv (by simp)
  have hm := LocalSobolev.memLp_bounded_smul hf hχ.continuous hB₀
  have hmD := (LocalSobolev.memLp_bounded_smulRight hf hχD hB₁).add
    (LocalSobolev.memLp_bounded_smul hD hχ.continuous hB₀)
  refine ⟨(hm.locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    (hmD.locallyIntegrable (by norm_num)).locallyIntegrableOn univ, ?_⟩
  intro ψ hψ hc _ v
  have htest := hw.2.2 (ψ * χ) (hψ.mul hχ) hc.mul_right (subset_univ _) v
  have hψd : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x ↦ fderiv ℝ ψ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L v) rfl
  have hi₁ : Integrable (fun x ↦ (ψ x * fderiv ℝ χ x v) • f x) μ :=
    (locallyIntegrableOn_univ.mp hw.1).integrable_smul_left_of_hasCompactSupport
      (hψ.continuous.mul (hχD.clm_apply continuous_const)) hc.mul_right
  have hi₂ : Integrable (fun x ↦ (χ x * fderiv ℝ ψ x v) • f x) μ :=
    (locallyIntegrableOn_univ.mp hw.1).integrable_smul_left_of_hasCompactSupport
      (hχ.continuous.mul hψd) hψdc.mul_left
  have hi₃ : Integrable (fun x ↦ (ψ x * χ x) • D x v) μ := by
    simpa using (ContinuousLinearMap.apply ℝ F v).integrable_comp
      ((locallyIntegrableOn_univ.mp hw.2.1).integrable_smul_left_of_hasCompactSupport
        (hψ.continuous.mul hχ.continuous) hc.mul_right)
  have hd (x : E) : fderiv ℝ (ψ * χ) x v =
      ψ x * fderiv ℝ χ x v + χ x * fderiv ℝ ψ x v := by
    rw [fderiv_mul (hψ.differentiable (by simp) x) (hχ.differentiable (by simp) x)]
    rfl
  simp only [hd, add_smul] at htest
  rw [integral_add hi₁ hi₂] at htest
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_add, smul_smul]
  rw [integral_add hi₁ hi₃]
  have heq : (fun x ↦ (fderiv ℝ ψ x v * χ x) • f x) =
      (fun x ↦ (χ x * fderiv ℝ ψ x v) • f x) := by
    funext x
    rw [mul_comm]
  rw [heq]
  change (∫ x, (ψ x * fderiv ℝ χ x v) • f x ∂μ) +
    (∫ x, (ψ x * χ x) • D x v ∂μ) = _
  change (∫ x, (ψ x * χ x) • D x v ∂μ) = _ at htest
  rw [htest]
  abel

end JanetCartan.Mollification
