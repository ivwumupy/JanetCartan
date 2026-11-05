module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Basic

/-!
# Fourier normalization and frequency Jacobians

Both independent time/transverse covectors are rescaled in
`app:ch_regular:lem:finite-chain`. This contributes `ρ^(2(1+dim E))`.
The base and normal coordinates are not rescaled. The radian normalization is
also checked directly against the cycles convention of Mathlib.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local instance : (volume : Measure (ℝ × E)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure E)

local instance : (volume : Measure ((ℝ × E) × (ℝ × E))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ × E)) (volume : Measure (ℝ × E))

/-- The single-frequency radian normalization agrees with changing from
cycles to radians (`app:ch_regular:lem:finite-chain`). -/
theorem normalization_smul_integral (f : ℝ × E → ℂ) :
    normalization (E := E) • (∫ ξ, f ξ) = ∫ ξ, f ((2 * Real.pi) • ξ) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f (2 * Real.pi)
    (hR := by positivity)]
  congr 1
  simp only [normalization, Module.finrank_prod, Module.finrank_self]
  exact inv_pow _ _

/-- The two independent frequency measures each contribute their Fourier
normalization (`app:ch_regular:lem:finite-chain`). -/
theorem normalization_sq_smul_integral (f : ((ℝ × E) × (ℝ × E)) → ℂ) :
    (normalization (E := E)) ^ 2 • (∫ ω, f ω) = ∫ ω, f ((2 * Real.pi) • ω) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f (2 * Real.pi)
    (hR := by positivity)]
  congr 1
  simp only [normalization, Module.finrank_prod, Module.finrank_self]
  rw [pow_two, ← pow_add, inv_pow]

/-- Joint frequency rescaling has the full Jacobian, including the two time
frequencies (`app:ch_regular:lem:finite-chain`). -/
theorem integral_frequencyPair_rescale (f : ((ℝ × E) × (ℝ × E)) → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ ω, f ω) = ρ ^ (2 * (1 + Module.finrank ℝ E)) • ∫ ω, f (ρ • ω) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f ρ (hR := hρ.le), smul_smul]
  have hrank : Module.finrank ℝ ((ℝ × E) × (ℝ × E)) =
      2 * (1 + Module.finrank ℝ E) := by
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  rw [hrank, mul_inv_cancel₀ (pow_ne_zero _ hρ.ne'), one_smul]

/-- Exact normalized lower kernel: the phase is `ρ * packedPhase`, the
amplitude samples both covectors at scale `ρ`, and the Jacobian is explicit
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`).
This is a change-of-variables identity; absolute convergence and operator
identification are separate statements. -/
theorem lowerFourierKernel_rescale (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) {ρ : ℝ} (hρ : 0 < ρ) :
    lowerFourierKernel α β mi mo r xi xo =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, ∫ ω : (ℝ × E) × (ℝ × E),
          Complex.exp (((ρ * packedPhase xi xo (d, b, ω) : ℝ) : ℂ) * Complex.I) *
            lowerAmplitude α β mi mo r xi xo (d, b, ρ • ω) := by
  unfold lowerFourierKernel
  simp_rw [integral_frequencyPair_rescale (fun ω =>
    lowerIntegrand α β mi mo r xi xo (_, _, ω)) hρ]
  have he (d : ℝ) (b : ℝ × E) (ω : (ℝ × E) × (ℝ × E)) :
      lowerIntegrand α β mi mo r xi xo (d, b, ρ • ω) =
        Complex.exp (((ρ * packedPhase xi xo (d, b, ω) : ℝ) : ℂ) * Complex.I) *
          lowerAmplitude α β mi mo r xi xo (d, b, ρ • ω) := by
    unfold lowerIntegrand
    rw [show packedPhase xi xo (d, b, ρ • ω) = ρ * packedPhase xi xo (d, b, ω) from
      packedPhase_frequency_smul xi xo b ω.1 ω.2 d ρ]
  simp_rw [he, integral_smul, smul_smul]

/-- The literal upper kernel has the same Jacobian and its own reversed
phase and exchanged weights (`app:ch_regular:lem:finite-chain`). -/
theorem upperFourierKernel_rescale (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) {ρ : ℝ} (hρ : 0 < ρ) :
    upperFourierKernel α β mi mo r xi xo =
      ((normalization (E := E)) ^ 2 * ρ ^ (2 * (1 + Module.finrank ℝ E))) •
        ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, ∫ ω : (ℝ × E) × (ℝ × E),
          Complex.exp (((ρ * packedUpperPhase xi xo (d, b, ω) : ℝ) : ℂ) * Complex.I) *
            upperAmplitude α β mi mo r xi xo (d, b, ρ • ω) := by
  unfold upperFourierKernel
  simp_rw [integral_frequencyPair_rescale (fun ω =>
    upperIntegrand α β mi mo r xi xo (_, _, ω)) hρ]
  have he (d : ℝ) (b : ℝ × E) (ω : (ℝ × E) × (ℝ × E)) :
      upperIntegrand α β mi mo r xi xo (d, b, ρ • ω) =
        Complex.exp (((ρ * packedUpperPhase xi xo (d, b, ω) : ℝ) : ℂ) * Complex.I) *
          upperAmplitude α β mi mo r xi xo (d, b, ρ • ω) := by
    unfold upperIntegrand
    rw [show packedUpperPhase xi xo (d, b, ρ • ω) =
        ρ * packedUpperPhase xi xo (d, b, ω) from
      packedUpperPhase_frequency_smul xi xo b ω.1 ω.2 d ρ]
  simp_rw [he, integral_smul, smul_smul]

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
