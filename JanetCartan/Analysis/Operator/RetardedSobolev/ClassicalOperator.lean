module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Smooth
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Classical

/-!
# Retarded operators on smooth compactly supported fields

The actual lower and upper integrals act linearly on test fields, as needed for
completion in `app:ch_osc:prop:osc-retarded-tube`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

variable {d : ℕ}

/-- The literal lower integral as a complex-linear map on smooth tests
(`app:ch_osc:setup:osc-retarded`). -/
def lowerTest (a : ℝ) (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsout : HasCompactSupport χout) : Spaces.Test d →ₗ[ℂ] Spaces.Test d where
  toFun f := ⟨Retarded.lower a χin χout f,
    contDiff_lower a hin hout f.property.1, hasCompactSupport_lower a χin χout f hsout⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change Retarded.lower a χin χout (f + g) x =
      Retarded.lower a χin χout f x + Retarded.lower a χin χout g x
    simp only [Retarded.lower, Pi.add_apply, mul_add]
    rw [intervalIntegral.integral_add]
    · ring
    · exact ((Complex.continuous_ofReal.comp hin.continuous).mul f.property.1.continuous
        |>.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact ((Complex.continuous_ofReal.comp hin.continuous).mul g.property.1.continuous
        |>.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change Retarded.lower a χin χout (fun z ↦ c * f.val z) x =
      c * Retarded.lower a χin χout f x
    exact Retarded.lower_mul_transverse a χin χout f (fun _ ↦ c) x

/-- The literal upper adjoint as a complex-linear map on smooth tests
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
def upperTest (b : ℝ) (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) : Spaces.Test d →ₗ[ℂ] Spaces.Test d where
  toFun f := ⟨Retarded.upper b χin χout f,
    contDiff_upper b hin hout f.property.1, hasCompactSupport_upper b χin χout f hsin⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change Retarded.upper b χin χout (f + g) x =
      Retarded.upper b χin χout f x + Retarded.upper b χin χout g x
    simp only [Retarded.upper, Pi.add_apply, mul_add]
    rw [intervalIntegral.integral_add]
    · ring
    · exact ((Complex.continuous_ofReal.comp hout.continuous).mul f.property.1.continuous
        |>.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact ((Complex.continuous_ofReal.comp hout.continuous).mul g.property.1.continuous
        |>.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change Retarded.upper b χin χout (fun z ↦ c * f.val z) x =
      c * Retarded.upper b χin χout f x
    exact Retarded.upper_mul_transverse b χin χout f (fun _ ↦ c) x

/-- The lower integral is supported in its outer cutoff
(`app:ch_osc:setup:osc-retarded`). -/
theorem tsupport_lower_subset (a : ℝ) (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (f : ℝ × (Fin d → ℝ) → ℂ) :
    tsupport (Retarded.lower a χin χout f) ⊆ tsupport χout := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
  simp [Retarded.lower, hx]

/-- The upper adjoint is supported in its outer cutoff `χin`
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem tsupport_upper_subset (b : ℝ) (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (f : ℝ × (Fin d → ℝ) → ℂ) :
    tsupport (Retarded.upper b χin χout f) ⊆ tsupport χin := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
  simp [Retarded.upper, hx]

end JanetCartan.RetardedSobolev
