module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Composition.Physical

/-!
# The actual regularized retarded composition

The identities here identify the physical left/right quantizations with the
concrete Fourier kernels in `app:ch_regular:lem:finite-chain`, “Retarded and
signed factors”. All Fubini hypotheses follow from smoothness and compact
support. The lower and literal upper positive input buffers are retained.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The full regularized lower composition identity, with its fixed positive
input buffer and no extra output-support premise
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem leftOperator_imaginary_lower_rightOperator_eq_integral
    (a ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (_hso : HasCompactSupport (Function.uncurry mo))
    (hsr : HasCompactSupport r) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, s ≤ a+ε → β (s,y) = 0) (xo : ℝ × E) :
    leftOperator (complementarySymbol r mo)
      (fun z => Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) z) xo =
      ∫ xi, lowerFourierKernel α β mi mo r xi xo * u xi := by
  have hL : Continuous (fun z => leftKernel (complementarySymbol r mo) xo z) :=
    (contDiff_leftKernel_complementarySymbol mo r ho hr hsr).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hf := (contDiff_rightOperator mi u hi hsi hu hsu).continuous
  have hF := integrable_lowerCompositionIntegrand α β mi mo r u xo
    hα.continuous hβ.continuous hi ho hr hu.continuous hsα hsβ hsi hsr hsu
  unfold leftOperator
  simp_rw [show ∀ z : ℝ × E,
    Complex.I * JanetCartan.Retarded.lower a β α (rightOperator mi u) z = _ from
      fun z => imaginary_lower_eq_normal_of_input_buffer a ε hε α β hbuffer
        (rightOperator mi u) z.1 z.2]
  rw [integral_lower_normal_translation α β _ _ hα.continuous hβ.continuous hL hf hsα hsβ]
  simp_rw [lowerFourierKernel_eq_fiberComposition, ← integral_mul_const]
  simpa only [lowerCompositionIntegrand, rightOperator, ← integral_const_mul, mul_assoc]
    using integral_source_normal_base_swap _ hF

/-- The full regularized literal upper composition identity, with its fixed positive
input buffer and no extra output-support premise
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem leftOperator_imaginary_upper_rightOperator_eq_integral
    (b ε : ℝ) (hε : 0 < ε)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi)) (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (hr : ContDiff ℝ ∞ r) (hu : ContDiff ℝ ∞ u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi))
    (_hso : HasCompactSupport (Function.uncurry mo))
    (hsr : HasCompactSupport r) (hsu : HasCompactSupport u)
    (hbuffer : ∀ s y, b-ε ≤ s → α (s,y) = 0) (xo : ℝ × E) :
    leftOperator (complementarySymbol r mo)
      (fun z => -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) z) xo =
      ∫ xi, upperFourierKernel α β mi mo r xi xo * u xi := by
  have hL : Continuous (fun z => leftKernel (complementarySymbol r mo) xo z) :=
    (contDiff_leftKernel_complementarySymbol mo r ho hr hsr).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hf := (contDiff_rightOperator mi u hi hsi hu hsu).continuous
  have hF := integrable_upperCompositionIntegrand α β mi mo r u xo
    hα.continuous hβ.continuous hi ho hr hu.continuous hsα hsβ hsi hsr hsu
  unfold leftOperator
  simp_rw [show ∀ z : ℝ × E,
    -Complex.I * JanetCartan.Retarded.upper b β α (rightOperator mi u) z = _ from
      fun z => imaginary_upper_eq_normal_of_input_buffer b ε hε α β hbuffer
        (rightOperator mi u) z.1 z.2]
  rw [integral_upper_normal_swap α β _ _ hα.continuous hβ.continuous hL hf hsα hsβ]
  simp_rw [upperFourierKernel_eq_fiberComposition, ← integral_mul_const]
  simpa only [upperCompositionIntegrand, rightOperator, ← integral_const_mul, mul_assoc]
    using integral_source_normal_base_swap _ hF

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
