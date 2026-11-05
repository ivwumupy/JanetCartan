module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Basic

/-!
# Integrating the two independent frequencies

For `app:ch_regular:lem:finite-chain`, the concrete packed integrands factor
into the two quantization characters and the literal retarded weights. Product
integration recovers the physical left and right kernels with both Fourier
normalizations. Absolute frequency integrability is proved for continuous
compactly supported frequency factors, separately from the exact identities.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact lower integrand factorization into the output and input Fourier
characters, keeping all amplitude positions (`app:ch_regular:lem:finite-chain`). -/
theorem lowerIntegrand_factorization (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b κ τ : ℝ × E) (d : ℝ) :
    lowerIntegrand α β mi mo r xi xo (d, b, κ, τ) =
      (Complex.I * (α (b.1+d,b.2) : ℂ) * (β b : ℂ)) *
        ((wave κ (xo - (b.1+d,b.2)) * (r κ * (1-mo xo κ))) *
          (wave τ (b-xi) * mi xi τ)) := by
  rw [lowerIntegrand, ← wave_mul_wave_lower]
  unfold lowerAmplitude
  ring

/-- Exact upper factorization, with `-i` and the upper input time
(`app:ch_regular:lem:finite-chain`). -/
theorem upperIntegrand_factorization (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b κ τ : ℝ × E) (d : ℝ) :
    upperIntegrand α β mi mo r xi xo (d, b, κ, τ) =
      (-Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ)) *
        ((wave κ (xo-b) * (r κ * (1-mo xo κ))) *
          (wave τ ((b.1+d,b.2)-xi) * mi xi τ)) := by
  rw [upperIntegrand, ← wave_mul_wave_upper]
  unfold upperAmplitude
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A compact frequency symbol times a Fourier character is absolutely
integrable (`app:ch_regular:lem:finite-chain`). -/
theorem integrable_wave_mul (m : ℝ × E → ℂ) (hm : Continuous m)
    (hms : HasCompactSupport m) (x : ℝ × E) :
    Integrable (fun ξ => wave ξ x * m ξ) := by
  have hw : Continuous (fun ξ => wave ξ x) := by
    unfold wave pairing
    fun_prop
  exact (hw.mul hm).integrable_of_hasCompactSupport hms.mul_left

/-- Absolute convergence in the frequency pair for the concrete lower
integrand follows from compact support of the regularizer and input symbol
(`app:ch_regular:lem:finite-chain`). -/
theorem integrable_lowerIntegrand_frequencies (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b : ℝ × E) (d : ℝ)
    (hi : Continuous (mi xi)) (his : HasCompactSupport (mi xi))
    (ho : Continuous (mo xo)) (hr : Continuous r) (hrs : HasCompactSupport r) :
    Integrable (fun ω : (ℝ × E) × (ℝ × E) => lowerIntegrand α β mi mo r xi xo (d,b,ω)) := by
  have hout := integrable_wave_mul (fun κ => r κ * (1-mo xo κ))
    (hr.mul (continuous_const.sub ho)) hrs.mul_right (xo-(b.1+d,b.2))
  have hin := integrable_wave_mul (mi xi) hi his (b-xi)
  have h := (hout.mul_prod hin).const_mul
    (Complex.I * (α (b.1+d,b.2) : ℂ) * (β b : ℂ))
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (lowerIntegrand_factorization α β mi mo r xi xo b ω.1 ω.2 d).symm)

/-- Absolute frequency convergence also holds for the literal adjoint
(`app:ch_regular:lem:finite-chain`). -/
theorem integrable_upperIntegrand_frequencies (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b : ℝ × E) (d : ℝ)
    (hi : Continuous (mi xi)) (his : HasCompactSupport (mi xi))
    (ho : Continuous (mo xo)) (hr : Continuous r) (hrs : HasCompactSupport r) :
    Integrable (fun ω : (ℝ × E) × (ℝ × E) => upperIntegrand α β mi mo r xi xo (d,b,ω)) := by
  have hout := integrable_wave_mul (fun κ => r κ * (1-mo xo κ))
    (hr.mul (continuous_const.sub ho)) hrs.mul_right (xo-b)
  have hin := integrable_wave_mul (mi xi) hi his ((b.1+d,b.2)-xi)
  have h := (hout.mul_prod hin).const_mul
    (-Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ))
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (upperIntegrand_factorization α β mi mo r xi xo b ω.1 ω.2 d).symm)

/-- Product frequency integration gives the literal left/right lower
kernel factors with both normalizations (`app:ch_regular:lem:finite-chain`). -/
theorem integral_lowerIntegrand_frequencies (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b : ℝ × E) (d : ℝ) :
    (normalization (E := E)) ^ 2 •
        (∫ ω : (ℝ × E) × (ℝ × E), lowerIntegrand α β mi mo r xi xo (d,b,ω)) =
      leftKernel (complementarySymbol r mo) xo (b.1+d,b.2) *
        (Complex.I * (α (b.1+d,b.2) : ℂ) * (β b : ℂ)) * rightKernel mi b xi := by
  simp_rw [show ∀ ω : (ℝ × E) × (ℝ × E),
    lowerIntegrand α β mi mo r xi xo (d,b,ω) = _ from fun ω =>
      lowerIntegrand_factorization α β mi mo r xi xo b ω.1 ω.2 d]
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul
    (μ := (volume : Measure (ℝ × E))) (ν := (volume : Measure (ℝ × E)))
    (fun κ => wave κ (xo-(b.1+d,b.2)) * (r κ * (1-mo xo κ)))
    (fun τ => wave τ (b-xi) * mi xi τ)]
  simp only [leftKernel, rightKernel, complementarySymbol, Complex.real_smul,
    Complex.ofReal_pow]
  ring

/-- Product frequency integration for the literal upper kernel
(`app:ch_regular:lem:finite-chain`). -/
theorem integral_upperIntegrand_frequencies (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo b : ℝ × E) (d : ℝ) :
    (normalization (E := E)) ^ 2 •
        (∫ ω : (ℝ × E) × (ℝ × E), upperIntegrand α β mi mo r xi xo (d,b,ω)) =
      leftKernel (complementarySymbol r mo) xo b *
        (-Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ)) *
          rightKernel mi (b.1+d,b.2) xi := by
  simp_rw [show ∀ ω : (ℝ × E) × (ℝ × E),
    upperIntegrand α β mi mo r xi xo (d,b,ω) = _ from fun ω =>
      upperIntegrand_factorization α β mi mo r xi xo b ω.1 ω.2 d]
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul
    (μ := (volume : Measure (ℝ × E))) (ν := (volume : Measure (ℝ × E)))
    (fun κ => wave κ (xo-b) * (r κ * (1-mo xo κ)))
    (fun τ => wave τ ((b.1+d,b.2)-xi) * mi xi τ)]
  simp only [leftKernel, rightKernel, complementarySymbol, Complex.real_smul,
    Complex.ofReal_pow]
  ring

/-- The lower joint Fourier integral equals the half-space composition of
the two quantization kernels (`app:ch_regular:lem:finite-chain`). -/
theorem lowerFourierKernel_eq_fiberComposition (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E) :
    lowerFourierKernel α β mi mo r xi xo =
      ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E,
        leftKernel (complementarySymbol r mo) xo (b.1+d,b.2) *
          (Complex.I * (α (b.1+d,b.2) : ℂ) * (β b : ℂ)) * rightKernel mi b xi := by
  unfold lowerFourierKernel
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with b
  exact integral_lowerIntegrand_frequencies α β mi mo r xi xo b d

/-- The upper joint integral equals the reversed half-space composition,
with the literal scalar `-i` (`app:ch_regular:lem:finite-chain`). -/
theorem upperFourierKernel_eq_fiberComposition (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ) (xi xo : ℝ × E) :
    upperFourierKernel α β mi mo r xi xo =
      ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E,
        leftKernel (complementarySymbol r mo) xo b *
          (-Complex.I * (β b : ℂ) * (α (b.1+d,b.2) : ℂ)) *
            rightKernel mi (b.1+d,b.2) xi := by
  unfold upperFourierKernel
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with b
  exact integral_upperIntegrand_frequencies α β mi mo r xi xo b d

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
