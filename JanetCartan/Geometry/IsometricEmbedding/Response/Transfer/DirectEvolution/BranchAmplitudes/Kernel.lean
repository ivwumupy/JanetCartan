module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.KernelIdentity

/-!
# Literal graph kernel of a restored carrier branch

The amplitude of `new:eq:carrier-ibp` is restored at the original covector,
without changing the full graph phase. The physical Fourier normalization,
covector Jacobian and order factor are all retained. This supplies the exact
kernel identification for the low-operator/Sobolev assembly of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
open CompactTransfer FourierIntegral

variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The restored branch evaluates to the same differentiated matrix
expression at `ξ=λθ`, with exactly its original order factor `λ^p`.
Source: restoring the carrier after `new:eq:carrier-ibp`. -/
theorem modifiedAmplitude_normalizedTerm_apply
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (Euclidean n × P) → CarrierVariables n → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → Mat)
    (t : JointTransferTerm n P Mat ι) (c : P)
    {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) (x z θ : Euclidean n) :
    ModifiedLow.modifiedAmplitude lam p (normalizedTermAmplitude b f w₀ α t c)
        x z (lam • θ) =
      (lam ^ p) • (t.amplitude.evaluate (jointAmplitudeFields b f w₀ α)
        ((x, c), WithLp.toLp 2 (z, θ))).1 := by
  simp only [ModifiedLow.modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
    smul_smul, inv_mul_cancel₀ hlam, one_smul, Pi.smul_apply,
    normalizedTermAmplitude, matrixSlice, normalizedSlice]

/-- Exact demodulated forward graph kernel for a literal transfer branch.
The phase is the original `Θ`, specialized to `elapsedPhase Ψ r` by the
consumer. The original input is still differentiated by `t.datumWord` in
the compact expansion; here `a` is that datum. No operator estimate or
transfer identity is assumed (`new:eq:carrier-ibp`). -/
theorem demodulated_branchGraphOperator_eq_normalized
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → Mat)
    (t : JointTransferTerm n P Mat ι) (c : P)
    (a : Euclidean n → Fin r → ℂ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (x : Euclidean n)
    (hΘ : ∀ z θ,
      ModifiedLow.modifiedAmplitude lam p
        (normalizedTermAmplitude b (carrierPhase Θ φ) w₀ α t c) x z (lam • θ) ≠ 0 →
      Θ x (lam • θ) = lam * Θ x θ) :
    carrier (-lam) (fun y => φ y c) x •
      graphOperator Θ (ModifiedLow.modifiedAmplitude lam p
        (normalizedTermAmplitude b (carrierPhase Θ φ) w₀ α t c))
        (fun z => carrier lam (fun y => φ y c) z • a z) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (lam ^ n •
        ∫ θ : Euclidean n, ∫ z : Euclidean n,
          oscillation (carrierPhase Θ φ) lam (x, c) (WithLp.toLp 2 (z, θ)) •
            ((lam ^ p) • (t.amplitude.evaluate
              (jointAmplitudeFields b (carrierPhase Θ φ) w₀ α)
                ((x, c), WithLp.toLp 2 (z, θ))).1).mulVec (a z)) := by
  rw [demodulated_graphOperator_eq_normalized _ _ _ _ hlam (x, c) hΘ]
  simp only [modifiedAmplitude_normalizedTerm_apply b _ w₀ α t c hlam.ne' p]

/-- Exact kernel of a branch for the literal reversed phase. The amplitude
is exchanged back to the original graph's physical positions before calling
`reverseGraphOperator`; its matrix action is unchanged. Equivalently this is
the literal adjoint kernel of the exchanged conjugate-transposed amplitude.
Source: the adjoint form of `new:eq:carrier-ibp`. -/
theorem demodulated_reverseBranchGraphOperator_eq_normalized
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (w₀ : (Euclidean n × P) → CarrierVariables n)
    (α : (Euclidean n × P) → CarrierVariables n → Mat)
    (t : JointTransferTerm n P Mat ι) (c : P)
    (a : Euclidean n → Fin r → ℂ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (x : Euclidean n)
    (hΘ : ∀ z θ,
      ModifiedLow.modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase Θ φ) w₀ α t c) x z (lam • θ) ≠ 0 →
      Θ z (lam • θ) = lam * Θ z θ) :
    carrier (-lam) (fun y => φ y c) x •
      reverseGraphOperator Θ (fun y z ξ => ModifiedLow.modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase Θ φ) w₀ α t c) z y ξ)
        (fun z => carrier lam (fun y => φ y c) z • a z) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (lam ^ n •
        ∫ θ : Euclidean n, ∫ z : Euclidean n,
          oscillation (adjointCarrierPhase Θ φ) lam (x, c) (WithLp.toLp 2 (z, θ)) •
            ((lam ^ p) • (t.amplitude.evaluate
              (jointAmplitudeFields b (adjointCarrierPhase Θ φ) w₀ α)
                ((x, c), WithLp.toLp 2 (z, θ))).1).mulVec (a z)) := by
  let A := ModifiedLow.modifiedAmplitude lam p
    (normalizedTermAmplitude b (adjointCarrierPhase Θ φ) w₀ α t c)
  have h := demodulated_reverseGraphOperator_eq_normalized Θ φ
    (fun y z ξ => (A z y ξ).conjTranspose) a hlam (x, c)
    (fun z θ hz => hΘ z θ (by
      intro hzero
      apply hz
      change (A x z (lam • θ)).conjTranspose = 0
      rw [show A x z (lam • θ) = 0 from hzero, Matrix.conjTranspose_zero]))
  simpa only [Matrix.conjTranspose_conjTranspose, A,
    modifiedAmplitude_normalizedTerm_apply b _ w₀ α t c hlam.ne' p] using h

end JanetCartan.ResponseTransfer.DirectEvolution.BranchAmplitudes
