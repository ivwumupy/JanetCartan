module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.PackedPhase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.BufferedKernel
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Concrete amplitudes for localized retarded kernels

Definitions for `app:ch_regular:lem:finite-chain`, “Retarded and signed factors”.
All frequencies in this module are radians. Each frequency integral carries
`(2π)⁻ⁿ`, where `n = 1 + dim E`. The transverse delta has already been applied:
both weights use the same transverse base. The output regularizer is explicit;
setting it to one does not assert convergence of the resulting integral.

The input mask is a right symbol, evaluated at the external input base, and
the output mask is a left symbol, evaluated at the external output base.
These definitions do not assert identification with the operator composition.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Time/transverse covector pairing in the radian convention
(`app:ch_regular:lem:finite-chain`). -/
def pairing (ξ x : ℝ × E) : ℝ := ξ.1 * x.1 + inner ℝ ξ.2 x.2

/-- The radian Fourier character in `app:ch_regular:lem:finite-chain`. -/
def wave (ξ x : ℝ × E) : ℂ := Complex.exp ((pairing ξ x : ℂ) * Complex.I)

/-- The literal upper phase on the same packed variables as `packedPhase`
(`app:ch_regular:lem:finite-chain`). Here the common base is the earlier time,
and the input is at that time plus `d`. -/
def packedUpperPhase (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℝ :=
  adjointPhase xi xo x.1 x.2.1.1 x.2.1.2 x.2.2.1.1 x.2.2.1.2
    x.2.2.2.1 x.2.2.2.2

/-- Lower amplitude with both literal weight positions, the scalar `i`, and
the entire regularized complementary output symbol
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
def lowerAmplitude (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  Complex.I * (α (x.2.1.1 + x.1, x.2.1.2) : ℂ) * (β x.2.1 : ℂ) *
    (r x.2.2.1 * (1 - mo xo x.2.2.1)) * mi xi x.2.2.2

/-- Upper amplitude for the literal adjoint of `i α H β`: its scalar is
`-i` and the weights are exchanged (`app:ch_regular:lem:finite-chain`). -/
def upperAmplitude (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  -Complex.I * (β x.2.1 : ℂ) * (α (x.2.1.1 + x.1, x.2.1.2) : ℂ) *
    (r x.2.2.1 * (1 - mo xo x.2.2.1)) * mi xi x.2.2.2

/-- Lower joint integrand, before its half-space integral
(`app:ch_regular:lem:finite-chain`). -/
def lowerIntegrand (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  Complex.exp ((packedPhase xi xo x : ℂ) * Complex.I) * lowerAmplitude α β mi mo r xi xo x

/-- Literal-adjoint joint integrand (`app:ch_regular:lem:finite-chain`). -/
def upperIntegrand (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) (x : ℝ × TangentialVariables E) : ℂ :=
  Complex.exp ((packedUpperPhase xi xo x : ℂ) * Complex.I) *
    upperAmplitude α β mi mo r xi xo x

/-- The exact two-character factorization of the lower packed phase
(`app:ch_regular:lem:finite-chain`). -/
theorem wave_mul_wave_lower (xi xo b κ τ : ℝ × E) (d : ℝ) :
    wave κ (xo - (b.1 + d, b.2)) * wave τ (b - xi) =
      Complex.exp ((packedPhase xi xo (d, b, κ, τ) : ℂ) * Complex.I) := by
  rw [wave, wave, ← Complex.exp_add]
  congr 1
  have hp : pairing κ (xo - (b.1 + d, b.2)) + pairing τ (b - xi) =
      packedPhase xi xo (d, b, κ, τ) := by
    simp only [pairing, packedPhase, phase, Prod.fst_sub, Prod.snd_sub,
      real_inner_comm κ.2, real_inner_comm τ.2]
    ring
  rw [← add_mul, ← Complex.ofReal_add, hp]

/-- The literal upper phase has the reversed translation
(`app:ch_regular:lem:finite-chain`). -/
theorem wave_mul_wave_upper (xi xo b κ τ : ℝ × E) (d : ℝ) :
    wave κ (xo - b) * wave τ ((b.1 + d, b.2) - xi) =
      Complex.exp ((packedUpperPhase xi xo (d, b, κ, τ) : ℂ) * Complex.I) := by
  rw [wave, wave, ← Complex.exp_add]
  congr 1
  have hp : pairing κ (xo - b) + pairing τ ((b.1 + d, b.2) - xi) =
      packedUpperPhase xi xo (d, b, κ, τ) := by
    simp only [pairing, packedUpperPhase, adjointPhase, Prod.fst_sub, Prod.snd_sub,
      real_inner_comm κ.2, real_inner_comm τ.2]
    ring
  rw [← add_mul, ← Complex.ofReal_add, hp]

/-- Packed literal-adjoint phase reversal; no signed partner is involved
(`app:ch_regular:lem:finite-chain`). -/
theorem packedUpperPhase_eq_neg_swap (xi xo b κ τ : ℝ × E) (d : ℝ) :
    packedUpperPhase xi xo (d, b, κ, τ) = -packedPhase xo xi (d, b, τ, κ) :=
  adjointPhase_eq_neg_swap xi xo d b.1 b.2 κ.1 κ.2 τ.1 τ.2

/-- The lower phase is linear under joint frequency normalization
(`app:ch_regular:lem:finite-chain`). -/
theorem packedPhase_frequency_smul (xi xo b κ τ : ℝ × E) (d ρ : ℝ) :
    packedPhase xi xo (d, b, ρ • κ, ρ • τ) = ρ * packedPhase xi xo (d, b, κ, τ) := by
  simp only [packedPhase, phase, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inner_smul_right]
  ring

/-- The upper phase has the same frequency normalization
(`app:ch_regular:lem:finite-chain`). -/
theorem packedUpperPhase_frequency_smul (xi xo b κ τ : ℝ × E) (d ρ : ℝ) :
    packedUpperPhase xi xo (d, b, ρ • κ, ρ • τ) =
      ρ * packedUpperPhase xi xo (d, b, κ, τ) := by
  rw [packedUpperPhase_eq_neg_swap, packedPhase_frequency_smul,
    packedUpperPhase_eq_neg_swap, mul_neg]

section Integrals
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One radian Fourier normalization, with the time dimension included
(`app:ch_regular:lem:finite-chain`). -/
def normalization : ℝ := (2 * Real.pi)⁻¹ ^ (1 + Module.finrank ℝ E)

/-- The actual right-symbol kernel, evaluated at its source base
(`app:ch_regular:lem:finite-chain`). -/
def rightKernel (m : (ℝ × E) → (ℝ × E) → ℂ) (x y : ℝ × E) : ℂ :=
  (normalization (E := E) : ℂ) * ∫ ξ, wave ξ (x - y) * m y ξ

/-- The actual left-symbol kernel, evaluated at its target base
(`app:ch_regular:lem:finite-chain`). -/
def leftKernel (m : (ℝ × E) → (ℝ × E) → ℂ) (x y : ℝ × E) : ℂ :=
  (normalization (E := E) : ℂ) * ∫ ξ, wave ξ (x - y) * m x ξ

/-- The right input quantization in `app:ch_regular:lem:finite-chain`.
Compact base/frequency symbols make this kernel integral absolute. -/
def rightOperator (m : (ℝ × E) → (ℝ × E) → ℂ)
    (u : ℝ × E → ℂ) (x : ℝ × E) : ℂ := ∫ y, rightKernel m x y * u y

/-- Left quantization by its physical kernel. This definition is used only
for regularized symbols; it does not represent the identity by an ordinary
unregularized kernel (`app:ch_regular:lem:finite-chain`). -/
def leftOperator (m : (ℝ × E) → (ℝ × E) → ℂ)
    (u : ℝ × E → ℂ) (x : ℝ × E) : ℂ := ∫ y, leftKernel m x y * u y

/-- The frequency-regularized complementary output symbol, retaining the
identity contribution (`app:ch_regular:eq:chain-tail`). -/
def complementarySymbol (r : ℝ × E → ℂ) (mo : (ℝ × E) → (ℝ × E) → ℂ)
    (x ξ : ℝ × E) : ℂ := r ξ * (1 - mo x ξ)

/-- Concrete regularized lower Fourier kernel. The order is normal variable,
common base, then the pair of frequencies (`app:ch_regular:lem:finite-chain`). -/
def lowerFourierKernel (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) : ℂ :=
  ((normalization (E := E)) ^ 2 : ℝ) •
    ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, ∫ ω : (ℝ × E) × (ℝ × E),
      lowerIntegrand α β mi mo r xi xo (d, b, ω)

/-- Concrete regularized upper Fourier kernel with the literal scalar `-i`
(`app:ch_regular:lem:finite-chain`). -/
def upperFourierKernel (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r : ℝ × E → ℂ) (xi xo : ℝ × E) : ℂ :=
  ((normalization (E := E)) ^ 2 : ℝ) •
    ∫ d in Ici (0 : ℝ), ∫ b : ℝ × E, ∫ ω : (ℝ × E) × (ℝ × E),
      upperIntegrand α β mi mo r xi xo (d, b, ω)

end Integrals
end JanetCartan.FiniteChain.Retarded.LocalizedKernel
