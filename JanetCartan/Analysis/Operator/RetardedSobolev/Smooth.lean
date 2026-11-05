module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Concrete
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Joint smoothness of the literal retarded operators

For `app:ch_osc:prop:osc-retarded-tube`, change variables to a fixed unit interval
and use the shared compact-parameter integration theorem. Both the time variable
and all transverse variables are retained. This supplies the regularity needed
for repeated Leibniz expansions of the weighted operators.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

variable {Y E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Joint smoothness of a finite-time lower primitive, including its moving
endpoint (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem contDiff_lowerPrimitive_joint (a : ℝ) {g : ℝ × Y → E}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x : ℝ × Y ↦ ∫ s in a..x.1, g (s, x.2)) := by
  let G : (ℝ × Y) × ℝ → E := fun p ↦ g (a + (p.1.1 - a) * p.2, p.1.2)
  have hG : ContDiff ℝ ∞ G := hg.comp
    ((contDiff_const.add ((contDiff_fst.fst.sub contDiff_const).mul contDiff_snd)).prodMk
      contDiff_fst.snd)
  have hI : ContDiff ℝ ∞ (fun x : ℝ × Y ↦ ∫ s in (0 : ℝ)..1, G (x, s)) := by
    apply contDiffOn_univ.mp
    exact contDiffOn_unitIntervalParameterIntegral isOpen_univ isOpen_univ (subset_univ _)
      hG.contDiffOn
  have h : ContDiff ℝ ∞ (fun x : ℝ × Y ↦ (x.1 - a) •
      ∫ s in (0 : ℝ)..1, G (x, s)) :=
    (contDiff_fst.sub (contDiff_const (c := a))).smul hI
  convert h using 1
  funext x
  simpa only [G, Pi.smul_apply, mul_zero, add_zero, mul_one, add_sub_cancel] using
    (intervalIntegral.smul_integral_comp_add_mul (fun s ↦ g (s, x.2)) (a := 0) (b := 1)
      (x.1 - a) a).symm

/-- Joint smoothness of the upper primitive
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem contDiff_upperPrimitive_joint (b : ℝ) {g : ℝ × Y → E}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x : ℝ × Y ↦ ∫ s in x.1..b, g (s, x.2)) := by
  have heq : (fun x : ℝ × Y ↦ ∫ s in x.1..b, g (s, x.2)) =
      fun x ↦ -(∫ s in b..x.1, g (s, x.2)) := by
    funext x
    exact intervalIntegral.integral_symm (f := fun s ↦ g (s, x.2)) b x.1
  rw [heq]
  exact (contDiff_lowerPrimitive_joint b hg).neg

/-- The concrete lower operator preserves joint smoothness
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem contDiff_lower (a : ℝ) {χin χout : ℝ × Y → ℝ} {f : ℝ × Y → ℂ}
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Retarded.lower a χin χout f) := by
  exact (Complex.ofRealCLM.contDiff.comp hout).mul
    (contDiff_lowerPrimitive_joint a ((Complex.ofRealCLM.contDiff.comp hin).mul hf))

/-- The literal upper adjoint preserves joint smoothness
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem contDiff_upper (b : ℝ) {χin χout : ℝ × Y → ℝ} {f : ℝ × Y → ℂ}
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Retarded.upper b χin χout f) := by
  exact (Complex.ofRealCLM.contDiff.comp hin).mul
    (contDiff_upperPrimitive_joint b ((Complex.ofRealCLM.contDiff.comp hout).mul hf))

omit [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- The lower operator inherits the compact support of its exterior cutoff
(`app:ch_osc:setup:osc-retarded`); no support assumption on the input is needed. -/
theorem hasCompactSupport_lower (a : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hsout : HasCompactSupport χout) : HasCompactSupport (Retarded.lower a χin χout f) :=
  (hsout.comp_left Complex.ofReal_zero).mul_right

omit [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- The literal upper adjoint inherits the support of `χin`, its exterior
cutoff (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem hasCompactSupport_upper (b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hsin : HasCompactSupport χin) : HasCompactSupport (Retarded.upper b χin χout f) :=
  (hsin.comp_left Complex.ofReal_zero).mul_right

end JanetCartan.RetardedSobolev
