module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.KernelJets

/-!
# Literal complementary parameter kernels

Shared formulas for the final parameter paragraph of
`app:ch_response:thm:response-literal-transfer`. The scalar oscillation `O`,
amplitude `A`, physical frequency and cutoffs are fixed. The original source
`u c` varies with the parameter. Forward and weighted reverse specializations
retain both physical positions and the physical Fourier normalization.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

open FourierIntegral

variable {n r : ℕ} {P : Type*}
local notation "E" => Euclidean n

/-- The literal integrand, including the original source, moving selector,
and carrier pair. Used by the finite Leibniz and L² realization proofs for
`app:ch_response:thm:response-literal-transfer`. -/
def parameterGraphIntegrand (O : E → E → E → ℂ) (A : FullAmplitude n r)
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (x y η : E) : Fin r → ℂ :=
  O x y η • (complementaryCarrierCoefficient q ζ ψ ρ c x y η •
    (A x y η).mulVec (u c y))

/-- The compact-frequency literal graph with physical normalization. Compact
frequency support is a hypothesis of the differentiation theorems, not an
alteration of the source (`app:ch_response:thm:response-literal-transfer`). -/
def parameterGraphIntegral (O : E → E → E → ℂ) (A : FullAmplitude n r)
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (x : E) : Fin r → ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    ∫ η, ∫ y, parameterGraphIntegrand O A q ζ ψ ρ u c x y η

/-- Factoring the carrier out of the complete matrix amplitude is an exact
identity before integration (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegrand_eq_carrier_amplitude
    (O : E → E → E → ℂ) (A : FullAmplitude n r)
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (x y η : E) :
    parameterGraphIntegrand O A q ζ ψ ρ u c x y η =
      O x y η • (parameterCarrierFactor ψ ρ c x y •
        complementaryParameterFamily A q ζ ρ c x y η).mulVec (u c y) := by
  simp [parameterGraphIntegrand, complementaryCarrierCoefficient,
    complementaryParameterFamily, complementaryAmplitude, normalizedCarrierOffset,
    Matrix.smul_mulVec, smul_smul]

/-- The forward specialization is the demodulated original graph on the
original carrier source (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegral_forward
    (S : E → E → ℝ) (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (φ : P → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (x : E) :
    parameterGraphIntegral (graphOscillation S) A q ζ
        (forwardCarrierPhase ζ φ) ρ u c x =
      carrier (-ρ) (φ c) x • graphOperator S
        (complementaryParameterFamily A q ζ ρ c)
        (fun y ↦ carrier ρ (fun z ↦ inner ℝ z (ζ c)) y • u c y) x := by
  simp only [parameterGraphIntegral, parameterGraphIntegrand_eq_carrier_amplitude,
    parameterCarrierFactor_forward, Matrix.smul_mulVec, Matrix.mulVec_smul,
    graphOperator, mul_smul]
  simp_rw [smul_comm (graphOscillation S x _ _) (carrier (-ρ) (φ c) x)]
  simp only [integral_smul]
  exact smul_comm _ _ _

/-- The physical forward graph uses the original input carrier and has no
output demodulation. Its parameter derivatives are therefore obtained from
the same kernel theorem with this phase
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegral_physical_forward
    (S : E → E → ℝ) (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (ρ : ℝ) (u : P → E → Fin r → ℂ) (c : P) (x : E) :
    parameterGraphIntegral (graphOscillation S) A q ζ
        (fun b _ y ↦ inner ℝ y (ζ b)) ρ u c x =
      graphOperator S (complementaryParameterFamily A q ζ ρ c)
        (fun y ↦ carrier ρ (fun z ↦ inner ℝ z (ζ c)) y • u c y) x := by
  have hphase : forwardCarrierPhase ζ (fun _ _ ↦ 0) =
      (fun b _ y ↦ inner ℝ y (ζ b)) := by
    funext b a y
    simp only [forwardCarrierPhase, sub_zero]
  have h := parameterGraphIntegral_forward S A q ζ (fun _ _ ↦ 0) ρ u c x
  rw [hphase] at h
  simpa only [carrier, mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_smul] using h

/-- The reverse specialization retains the full original amplitude. Taking
`A = LowEnvelope.reverseFullAmplitude S U χs χt χg` retains precisely `j_S U⁻¹`
and the three original cutoffs (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegral_reverse
    (S : E → E → ℝ) (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (φ : P → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (y : E) :
    parameterGraphIntegral (fun y x η ↦ star (graphOscillation S x y η)) A q ζ
        (reverseCarrierPhase ζ φ) ρ u c y =
      carrier (-ρ) (fun z ↦ inner ℝ z (ζ c)) y •
        (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
          star (graphOscillation S x y η) •
            (complementaryParameterFamily A q ζ ρ c y x η).mulVec
              (carrier ρ (φ c) x • u c x)) := by
  simp only [parameterGraphIntegral, parameterGraphIntegrand_eq_carrier_amplitude,
    parameterCarrierFactor_reverse, Matrix.smul_mulVec, Matrix.mulVec_smul, mul_smul]
  simp_rw [smul_comm (star (graphOscillation S _ y _))
    (carrier (-ρ) (fun z ↦ inner ℝ z (ζ c)) y)]
  simp only [integral_smul]
  exact smul_comm _ _ _

/-- The physical reverse expression retains the nonlinear carrier on the
original source. The matrix amplitude can be the literal `j_S U⁻¹` amplitude
with both physical cutoffs (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegral_physical_reverse
    (S : E → E → ℝ) (A : FullAmplitude n r) (q : E → ℂ)
    (ζ : P → E) (φ : P → E → ℝ) (ρ : ℝ)
    (u : P → E → Fin r → ℂ) (c : P) (y : E) :
    parameterGraphIntegral (fun y x η ↦ star (graphOscillation S x y η)) A q ζ
        (fun b _ x ↦ φ b x) ρ u c y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
        star (graphOscillation S x y η) •
          (complementaryParameterFamily A q ζ ρ c y x η).mulVec
            (carrier ρ (φ c) x • u c x) := by
  simp only [parameterGraphIntegral, parameterGraphIntegrand_eq_carrier_amplitude,
    parameterCarrierFactor, carrier, Matrix.smul_mulVec, Matrix.mulVec_smul]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
