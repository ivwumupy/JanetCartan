module

public import JanetCartan.Analysis.Operator.Retarded
public import JanetCartan.Analysis.Operator.RetardedSobolev.Primitive
public import JanetCartan.Analysis.Operator.RetardedSobolev.Transverse

/-!
# Derivatives of the literal retarded operators

The time endpoint identities in `app:ch_osc:prop:osc-retarded-tube`, including
the derivatives of the exterior cutoffs. These use the shared operators rather
than introducing another version of retarded integration.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RetardedSobolev

variable {Y : Type*}

/-- Differentiation in the time coordinate of `app:ch_osc:setup:osc-retarded`. -/
def timeDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Y → E) (x : ℝ × Y) : E := deriv (fun t ↦ f (t, x.2)) x.1

/-- The lower endpoint formula with its exterior-cutoff term
(`app:ch_osc:prop:osc-retarded-tube`). No derivative of the input is required. -/
theorem timeDeriv_lower (a : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (t : ℝ) (hg : Continuous (fun s ↦ (χin (s, y) : ℂ) * f (s, y)))
    (hout : DifferentiableAt ℝ (fun s ↦ χout (s, y)) t) :
    timeDeriv (Retarded.lower a χin χout f) (t, y) =
      (χout (t, y) : ℂ) * ((χin (t, y) : ℂ) * f (t, y)) +
        Retarded.lower a χin (timeDeriv χout) f (t, y) := by
  have h := hasDerivAt_cutoff_lowerPrimitive hg hout.hasDerivAt a
  simpa only [timeDeriv, Retarded.lower, Complex.real_smul] using h.deriv

/-- The upper endpoint has negative sign, and the exterior weight is `χin`
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem timeDeriv_upper (b : ℝ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (t : ℝ) (hg : Continuous (fun s ↦ (χout (s, y) : ℂ) * f (s, y)))
    (hin : DifferentiableAt ℝ (fun s ↦ χin (s, y)) t) :
    timeDeriv (Retarded.upper b χin χout f) (t, y) =
      -((χin (t, y) : ℂ) * ((χout (t, y) : ℂ) * f (t, y))) +
        Retarded.upper b (timeDeriv χin) χout f (t, y) := by
  have h := hasDerivAt_cutoff_upperPrimitive hg hin.hasDerivAt b
  simpa only [timeDeriv, Retarded.upper, Complex.real_smul, mul_neg] using h.deriv

/-- With no exterior cutoff, every positive time derivative is the preceding
derivative of the weighted input (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem iteratedDeriv_lower_one (a : ℝ) (χin : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (t : ℝ) (j : ℕ)
    (hg : Continuous (fun s ↦ (χin (s, y) : ℂ) * f (s, y))) :
    iteratedDeriv (j + 1) (fun s ↦ Retarded.lower a χin (fun _ ↦ 1) f (s, y)) t =
      iteratedDeriv j (fun s ↦ (χin (s, y) : ℂ) * f (s, y)) t := by
  simpa only [Retarded.lower, Complex.ofReal_one, one_mul] using
    iteratedDeriv_lowerPrimitive hg a t j

/-- Positive time derivatives of the upper primitive
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem iteratedDeriv_upper_one (b : ℝ) (χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (y : Y) (t : ℝ) (j : ℕ)
    (hg : Continuous (fun s ↦ (χout (s, y) : ℂ) * f (s, y))) :
    iteratedDeriv (j + 1) (fun s ↦ Retarded.upper b (fun _ ↦ 1) χout f (s, y)) t =
      -iteratedDeriv j (fun s ↦ (χout (s, y) : ℂ) * f (s, y)) t := by
  simpa only [Retarded.upper, Complex.ofReal_one, one_mul] using
    iteratedDeriv_upperPrimitive hg b t j

end JanetCartan.RetardedSobolev
