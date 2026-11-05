module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Composition
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Reconstruction
public import JanetCartan.Analysis.Operator.RetardedSobolev.Smooth
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Exact localized retarded Fourier representation

For `app:ch_regular:lem:finite-chain`, “Retarded and signed factors”, and
`app:ch_regular:eq:chain-tail`, these identities remove the output frequency
regularizer from the actual composed operators. The right input quantization
is smooth; multiplication by the exterior retarded weight gives compact
support. Thus Fourier reconstruction applies to the concrete retarded output.

The unregularized representation is a limit of absolutely convergent kernel
integrals. This retains the identity contribution of `1 - mo` without assigning
it a compact frequency support or exchanging an unproved limit and integral.
The upper orientation is the literal adjoint orientation with scalar `-i`,
exchanged weights, and reversed translation; it is not a signed conjugate partner.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A fixed smooth frequency regularizer used in the exact Fourier representation
of `app:ch_regular:eq:chain-tail`. Its defining bump is one near zero and compactly
supported; the actual retarded operator and both proof masks remain fixed. -/
def frequencyRegularizer (R : ℝ) (ξ : ℝ × E) : ℂ :=
  (default : ContDiffBump (0 : ℝ × E)) (R⁻¹ • ξ)

/-- Pointwise reconstruction of the actual localized lower operator from its
concrete regularized Fourier kernels (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). All analytic hypotheses of composition and
reconstruction are discharged from smooth compact support and the fixed input
buffer. The kernel contains both radian Fourier normalizations. -/
theorem tendsto_integral_lowerFourierKernel
    (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (hso : HasCompactSupport (Function.uncurry mo)) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, s ≤ a + ε → β (s, y) = 0)
    (χ : ℝ × E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsχ : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (xo : ℝ × E) :
    Tendsto (fun R : ℝ => ∫ xi,
      lowerFourierKernel α β mi mo (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) xi xo * u xi) atTop
      (𝓝 (Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) xo -
        leftOperator mo (fun z =>
          Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) z) xo)) := by
  let v : ℝ × E → ℂ := fun z =>
    Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) z
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul
    (JanetCartan.RetardedSobolev.contDiff_lower a hβ hα
      (contDiff_rightOperator mi u hi hsi hu hsu))
  have hvs : HasCompactSupport v :=
    (JanetCartan.RetardedSobolev.hasCompactSupport_lower a β α
      (rightOperator mi u) hsα).mul_left
  have hrec := tendsto_leftOperator_complementarySymbol v hv hvs mo ho hso
    χ hχ hsχ hχ0 xo
  apply hrec.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hr : ContDiff ℝ ∞ (fun ξ : ℝ × E => (χ (R⁻¹ • ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_id.const_smul (R⁻¹)))
  have hrs : HasCompactSupport (fun ξ : ℝ × E => (χ (R⁻¹ • ξ) : ℂ)) :=
    (hsχ.comp_smul (inv_ne_zero hR.ne')).comp_left Complex.ofReal_zero
  exact leftOperator_imaginary_lower_rightOperator_eq_integral a ε hε α β mi mo
    (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) u hα hβ hi ho hr hu hsα hsβ hsi hso hrs hsu hbuffer xo

/-- Exact Fourier representation of `(I - Mout) A Min` for the lower
orientation, interpreted by frequency regularization
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
The frequency regularizer is constructed here, so the statement requires no
auxiliary cutoff or reconstruction hypothesis. -/
theorem localized_lower_eq_fourier_limit
    (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (hso : HasCompactSupport (Function.uncurry mo)) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, s ≤ a + ε → β (s, y) = 0)
    (xo : ℝ × E) :
    Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) xo -
        leftOperator mo (fun z =>
          Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) z) xo =
      Filter.limUnder atTop (fun R : ℝ => ∫ xi,
        lowerFourierKernel α β mi mo (frequencyRegularizer R) xi xo * u xi) := by
  let χ : ContDiffBump (0 : ℝ × E) := default
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le])
  exact (tendsto_integral_lowerFourierKernel a ε hε α β mi mo u hα hβ hi ho hu
    hsα hsβ hsi hso hsu hbuffer χ χ.contDiff χ.hasCompactSupport hχ0 xo).limUnder_eq.symm

/-- Pointwise reconstruction of the actual localized upper operator from its
concrete regularized Fourier kernels (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). All analytic hypotheses of composition and
reconstruction are discharged from smooth compact support and the fixed input
buffer. The kernel contains both radian Fourier normalizations. -/
theorem tendsto_integral_upperFourierKernel
    (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (hso : HasCompactSupport (Function.uncurry mo)) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, b - ε ≤ s → α (s, y) = 0)
    (χ : ℝ × E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsχ : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (xo : ℝ × E) :
    Tendsto (fun R : ℝ => ∫ xi,
      upperFourierKernel α β mi mo (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) xi xo * u xi) atTop
      (𝓝 (-Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) xo -
        leftOperator mo (fun z =>
          -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) z) xo)) := by
  let v : ℝ × E → ℂ := fun z =>
    -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) z
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul
    (JanetCartan.RetardedSobolev.contDiff_upper b hβ hα
      (contDiff_rightOperator mi u hi hsi hu hsu))
  have hvs : HasCompactSupport v :=
    (JanetCartan.RetardedSobolev.hasCompactSupport_upper b β α
      (rightOperator mi u) hsβ).mul_left
  have hrec := tendsto_leftOperator_complementarySymbol v hv hvs mo ho hso
    χ hχ hsχ hχ0 xo
  apply hrec.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hr : ContDiff ℝ ∞ (fun ξ : ℝ × E => (χ (R⁻¹ • ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_id.const_smul (R⁻¹)))
  have hrs : HasCompactSupport (fun ξ : ℝ × E => (χ (R⁻¹ • ξ) : ℂ)) :=
    (hsχ.comp_smul (inv_ne_zero hR.ne')).comp_left Complex.ofReal_zero
  exact leftOperator_imaginary_upper_rightOperator_eq_integral b ε hε α β mi mo
    (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) u hα hβ hi ho hr hu hsα hsβ hsi hso hrs hsu hbuffer xo

/-- Exact Fourier representation of `(I - Mout) A Min` for the upper
orientation, interpreted by frequency regularization
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
The frequency regularizer is constructed here, so the statement requires no
auxiliary cutoff or reconstruction hypothesis. -/
theorem localized_upper_eq_fourier_limit
    (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (hso : HasCompactSupport (Function.uncurry mo)) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, b - ε ≤ s → α (s, y) = 0)
    (xo : ℝ × E) :
    -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) xo -
        leftOperator mo (fun z =>
          -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) z) xo =
      Filter.limUnder atTop (fun R : ℝ => ∫ xi,
        upperFourierKernel α β mi mo (frequencyRegularizer R) xi xo * u xi) := by
  let χ : ContDiffBump (0 : ℝ × E) := default
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (by simp [χ.rIn_pos.le])
  exact (tendsto_integral_upperFourierKernel b ε hε α β mi mo u hα hβ hi ho hu
    hsα hsβ hsi hso hsu hbuffer χ χ.contDiff χ.hasCompactSupport hχ0 xo).limUnder_eq.symm

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
