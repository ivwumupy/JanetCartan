module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Coordinates

/-!
# First output derivative of the phased amplitude

The pointwise amplitude formula in the gain-one argument following
`app:ch_regular_base:eq:graph-derivative-transfer`, with the `2π` convention.
This module differentiates the integrand; differentiation of the actual
operator additionally requires the frequency-limit argument.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- `app:ch_regular_base:eq:fio-input`: differentiating the phase times a
scalar amplitude gives its physical derivative and the frequency multiplier. -/
theorem fderiv_fourierChar_mul (f : V → ℂ) (x y ξ v : V) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun z ↦ (Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * f z) x v =
      (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
        (fderiv ℝ f x v + (2 * Real.pi * Complex.I * (⟪ξ, v⟫ : ℝ)) * f x) := by
  have hl : HasFDerivAt (fun z : V ↦ ⟪ξ, z - y⟫) (innerSL ℝ ξ) x := by
    convert! ((innerSL ℝ ξ).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)) using 1
  have hp := (Real.hasDerivAt_fourierChar ⟪ξ, x - y⟫).hasFDerivAt.comp x hl
  convert! congrArg (fun L : V →L[ℝ] ℂ ↦ L v) (hp.mul hf.hasFDerivAt).fderiv using 1
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  change (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
      (fderiv ℝ f x v + (2 * Real.pi * Complex.I * (⟪ξ, v⟫ : ℝ)) * f x) =
    (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) * fderiv ℝ f x v +
      f x * ((⟪ξ, v⟫ : ℝ) • (2 * Real.pi * Complex.I * (Real.fourierChar ⟪ξ, x - y⟫ : ℂ)))
  simp only [Complex.real_smul]
  ring
open JanetCartan.AmplitudeBound

/-- `app:ch_regular_base:eq:fio-input`: the first output coordinate derivative
of the complete phased two-position amplitude is `outputDerivativeAmplitude`.
Both physical masks are included in `b`. -/
theorem fderiv_phasedPairedAmplitude_apply {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2*d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (x y ξ : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun z ↦ (Real.fourierChar ⟪ξ, z - y⟫ : ℂ) * b ξ (pairedPosition z y)) x
      (EuclideanSpace.single i 1) =
      (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) * outputDerivativeAmplitude b i ξ (pairedPosition x y) := by
  have hd := (hb ξ).differentiable (by simp)
  have h := fderiv_fourierChar_mul _ x y ξ (EuclideanSpace.single i 1)
    ((hd _).comp x (hasFDerivAt_pairedPosition_left x y).differentiableAt)
  convert! h using 1
  change (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) * outputDerivativeAmplitude b i ξ (pairedPosition x y) =
    (Real.fourierChar ⟪ξ, x - y⟫ : ℂ) *
      (fderiv ℝ (fun z ↦ b ξ (pairedPosition z y)) x (EuclideanSpace.single i 1) +
        (2 * Real.pi * Complex.I * (⟪ξ, EuclideanSpace.single i 1⟫ : ℝ)) * b ξ (pairedPosition x y))
  rw [fderiv_pairedPosition_left_apply _ hd]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, outputDerivativeAmplitude]

end JanetCartan.Pseudodifferential
