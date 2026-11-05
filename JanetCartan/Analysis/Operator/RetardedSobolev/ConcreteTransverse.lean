module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Concrete

/-!
# Transverse derivatives of the literal operators

The differentiation-under-the-integral step in
`app:ch_osc:prop:osc-retarded-tube`, in the time-first coordinates of `Retarded`.
The formula includes the exterior cutoff derivative; the interior cutoff is
included in the differentiated integrand.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RetardedSobolev

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ProperSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transverse differentiation in time-first coordinates, for
`app:ch_osc:prop:osc-retarded-tube`. The compact time interval and `C¹` input
supply the domination needed for differentiation under the integral. -/
theorem hasFDerivAt_timeIntegral_transverse {g : ℝ × Y → E}
    (hg : ContDiff ℝ 1 g) (a b : ℝ) (y : Y) :
    HasFDerivAt (fun z ↦ ∫ s in a..b, g (s, z))
      (∫ s in a..b, (fderiv ℝ g (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Y)) y := by
  apply hasFDerivAt_intervalIntegral_parameter
    (g := fun z s ↦ g (s, z))
    (g' := fun z s ↦ (fderiv ℝ g (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ Y))
    (hg.continuous.comp continuous_swap)
    (((hg.continuous_fderiv (by norm_num)).comp continuous_swap).clm_comp continuous_const)
  intro z s
  exact ((hg.differentiable (by norm_num)) (s, z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right s z)

/-- Full transverse derivative of the concrete lower operator, including both
cutoffs (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem hasFDerivAt_lower_transverse (a t : ℝ) (y : Y)
    (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hin : ContDiff ℝ 1 χin) (hout : ContDiff ℝ 1 χout) (hf : ContDiff ℝ 1 f) :
    HasFDerivAt (fun z ↦ Retarded.lower a χin χout f (t, z))
      (χout (t, y) •
          (∫ s in a..t, (fderiv ℝ (fun x ↦ (χin x : ℂ) * f x) (s, y)).comp
            (ContinuousLinearMap.inr ℝ ℝ Y)) +
        ((fderiv ℝ χout (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Y)).smulRight
          (∫ s in a..t, (χin (s, y) : ℂ) * f (s, y))) y := by
  have hg : ContDiff ℝ 1 (fun x ↦ (χin x : ℂ) * f x) :=
    (Complex.ofRealCLM.contDiff.comp hin).mul hf
  have hI := hasFDerivAt_timeIntegral_transverse hg a t y
  have hχ := ((hout.differentiable (by norm_num)) (t, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right t y)
  have h := hχ.smul hI
  change HasFDerivAt (fun z ↦ χout (t, z) • ∫ s in a..t,
    (χin (s, z) : ℂ) * f (s, z)) _ y at h
  simpa only [Retarded.lower, Function.comp_def, Complex.real_smul] using h

/-- Full transverse derivative of the concrete literal adjoint
(`app:ch_osc:eq:retarded-literal-adjoint`). The exterior weight is `χin`. -/
theorem hasFDerivAt_upper_transverse (b t : ℝ) (y : Y)
    (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hin : ContDiff ℝ 1 χin) (hout : ContDiff ℝ 1 χout) (hf : ContDiff ℝ 1 f) :
    HasFDerivAt (fun z ↦ Retarded.upper b χin χout f (t, z))
      (χin (t, y) •
          (∫ s in t..b, (fderiv ℝ (fun x ↦ (χout x : ℂ) * f x) (s, y)).comp
            (ContinuousLinearMap.inr ℝ ℝ Y)) +
        ((fderiv ℝ χin (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Y)).smulRight
          (∫ s in t..b, (χout (s, y) : ℂ) * f (s, y))) y := by
  have hg : ContDiff ℝ 1 (fun x ↦ (χout x : ℂ) * f x) :=
    (Complex.ofRealCLM.contDiff.comp hout).mul hf
  have hI := hasFDerivAt_timeIntegral_transverse hg t b y
  have hχ := ((hin.differentiable (by norm_num)) (t, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right t y)
  have h := hχ.smul hI
  change HasFDerivAt (fun z ↦ χin (t, z) • ∫ s in t..b,
    (χout (s, z) : ℂ) * f (s, z)) _ y at h
  simpa only [Retarded.upper, Function.comp_def, Complex.real_smul] using h

end JanetCartan.RetardedSobolev
