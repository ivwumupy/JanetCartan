module

public import JanetCartan.Analysis.Operator.RetardedSobolev.TransverseJets

/-!
# Transverse Leibniz identities with both cutoffs

The directional Leibniz rule for a real cutoff and complex input, used in
`app:ch_osc:prop:osc-retarded-tube`. Together with the smooth transverse jets,
this supplies the calculus step for iterating the mixed cutoff estimates.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Transverse Leibniz rule for a real cutoff and complex input
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem transverseDeriv_real_mul (v : Y) {χ : ℝ × Y → ℝ} {f : ℝ × Y → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) :
    transverseDeriv v (fun x ↦ (χ x : ℂ) * f x) = fun x ↦
      (χ x : ℂ) * transverseDeriv v f x + ((transverseDeriv v χ x : ℝ) : ℂ) * f x := by
  funext x
  have hχ' := ((hχ.comp (contDiff_prodMk_right x.1)).differentiable (by simp)) x.2
  have hf' := ((hf.comp (contDiff_prodMk_right x.1)).differentiable (by simp)) x.2
  have h := congrArg (fun L ↦ L v) (hχ'.hasFDerivAt.smul hf'.hasFDerivAt).fderiv
  simpa only [transverseDeriv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.smul_def', Function.comp_def, Complex.real_smul] using h

end JanetCartan.RetardedSobolev
