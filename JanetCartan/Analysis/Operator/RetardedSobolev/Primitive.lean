module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time derivatives of retarded primitives

These are the endpoint and time-derivative identities used in the proof of
`app:ch_osc:prop:osc-retarded-tube` in `paper.tex`. They concern ordinary interval
integrals, so they can be used for both the shared retarded operator and its literal
adjoint without defining either operator again. Sobolev estimates are not asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RetardedSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The lower primitive loses one time derivative, as in the proof of
`app:ch_osc:prop:osc-retarded-tube`. For continuous `g` the identity also holds for
Mathlib's total iterated derivative, without higher differentiability assumptions. -/
theorem iteratedDeriv_lowerPrimitive {g : ℝ → E} (hg : Continuous g)
    (a t : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun u ↦ ∫ s in a..u, g s) t = iteratedDeriv j g t := by
  rw [iteratedDeriv_succ']
  have h : deriv (fun u ↦ ∫ s in a..u, g s) = g :=
    funext (fun u ↦ Continuous.deriv_integral g hg a u)
  rw [h]

/-- The upper primitive has the opposite endpoint sign, for the literal adjoint in
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem iteratedDeriv_upperPrimitive {g : ℝ → E} (hg : Continuous g)
    (b t : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun u ↦ ∫ s in u..b, g s) t = -iteratedDeriv j g t := by
  rw [iteratedDeriv_succ']
  have h : deriv (fun u ↦ ∫ s in u..b, g s) = fun u ↦ -g u := by
    funext u
    exact (intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).deriv
  rw [h, iteratedDeriv_fun_neg]

/-- The endpoint term and output-cutoff term for the lower integral in
`app:ch_osc:setup:osc-retarded`; the input cutoff may be included in `g`. -/
theorem hasDerivAt_cutoff_lowerPrimitive {g : ℝ → E} (hg : Continuous g)
    {χ : ℝ → ℝ} {χ' t : ℝ} (hχ : HasDerivAt χ χ' t) (a : ℝ) :
    HasDerivAt (fun u ↦ χ u • ∫ s in a..u, g s)
      (χ t • g t + χ' • ∫ s in a..t, g s) t := by
  exact hχ.smul (hg.integral_hasStrictDerivAt a t).hasDerivAt

/-- The endpoint term and cutoff term for the upper integral in
`app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem hasDerivAt_cutoff_upperPrimitive {g : ℝ → E} (hg : Continuous g)
    {χ : ℝ → ℝ} {χ' t : ℝ} (hχ : HasDerivAt χ χ' t) (b : ℝ) :
    HasDerivAt (fun u ↦ χ u • ∫ s in u..b, g s)
      (χ t • (-g t) + χ' • ∫ s in t..b, g s) t := by
  exact hχ.smul (intervalIntegral.integral_hasDerivAt_left
    (hg.intervalIntegrable _ _) (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt)

/-- Commuting a time derivative past the lower primitive leaves the lower endpoint
value. The buffer in `app:ch_osc:setup:osc-retarded` makes this value zero for the
input-cutoff product. -/
theorem deriv_lowerPrimitive_sub_integral_deriv {g : ℝ → E}
    (hg : Differentiable ℝ g) (a t : ℝ)
    (hint : IntervalIntegrable (deriv g) volume a t) :
    deriv (fun u ↦ ∫ s in a..u, g s) t - (∫ s in a..t, deriv g s) = g a := by
  rw [Continuous.deriv_integral g hg.continuous,
    intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hg s) hint]
  abel

/-- The time-derivative commutator for the upper primitive has the negative upper
endpoint value; see `app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem deriv_upperPrimitive_sub_integral_deriv {g : ℝ → E}
    (hg : Differentiable ℝ g) (b t : ℝ)
    (hint : IntervalIntegrable (deriv g) volume t b) :
    deriv (fun u ↦ ∫ s in u..b, g s) t - (∫ s in t..b, deriv g s) = -g b := by
  rw [intervalIntegral.deriv_integral_left (hg.continuous.intervalIntegrable _ _)
      (hg.continuous.stronglyMeasurableAtFilter _ _) hg.continuous.continuousAt,
    intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hg s) hint]
  abel

/-- The lower primitive gains one classical time derivative
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem contDiff_lowerPrimitive {m : ℕ} {g : ℝ → E} (hg : ContDiff ℝ m g) (a : ℝ) :
    ContDiff ℝ (m + 1 : ℕ) (fun t ↦ ∫ s in a..t, g s) := by
  rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
  refine ⟨fun t ↦ (hg.continuous.integral_hasStrictDerivAt a t).hasDerivAt.differentiableAt,
    by simp, ?_⟩
  have heq : deriv (fun t ↦ ∫ s in a..t, g s) = g :=
    funext (fun t ↦ Continuous.deriv_integral g hg.continuous a t)
  rw [heq]
  exact hg

/-- The upper primitive gains one classical time derivative
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem contDiff_upperPrimitive {m : ℕ} {g : ℝ → E} (hg : ContDiff ℝ m g) (b : ℝ) :
    ContDiff ℝ (m + 1 : ℕ) (fun t ↦ ∫ s in t..b, g s) := by
  have h := (contDiff_lowerPrimitive hg b).neg
  convert h using 1
  funext t
  exact intervalIntegral.integral_symm (f := g) b t

end JanetCartan.RetardedSobolev
