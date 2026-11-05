module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators

/-!
# The initial literal adjoint annular branch

The full original amplitude, including both masks, beta/high-pass and the
annular multiplier, is exchanged and conjugate-transposed before normalization.
Restoration gives exactly the Hilbert adjoint of the original annular envelope,
for the literal-adjoint case of `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The literal adjoint initial amplitude in the normalized reverse carrier
variables: exchange physical positions, conjugate-transpose, evaluate at
`lam • θ`, and divide by `lam^p`. Every original cutoff is retained.
Source: the adjoint case of `new:eq:carrier-ibp`. -/
def normalizedAdjointAnnularElapsedAmplitude (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed lam : ℝ) (p : ℤ)
    (q : E × P) (w : CarrierVariables (d + 1)) : Mat :=
  (lam ^ p)⁻¹ • (annularElapsedAmplitude a χout χsource β π elapsed lam
    w.fst q.1 (lam • w.snd)).conjTranspose

/-- All original physical masks and frequency factors occur in the literal
reversed integrand, with the elapsed amplitude evaluated at the exchanged
output position (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalizedAdjointAnnularElapsedAmplitude_apply
    (a : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ)
    (q : E × P) (z θ : E) :
    normalizedAdjointAnnularElapsedAmplitude a χout χsource β π elapsed lam p
      q (WithLp.toLp 2 (z, θ)) =
      (lam ^ p)⁻¹ • (((π θ * (χout z * χsource q.1 * β (lam • θ))) •
        a (z 0) (z 0 - elapsed) (spatialPart z) (spatialPart (lam • θ))).conjTranspose) := by
  simp only [normalizedAdjointAnnularElapsedAmplitude, annularElapsedAmplitude,
    normalized_elapsedAmplitude_with_annular_mask a χout χsource β π hlam]
  rfl

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]

/-- The initial reversed branch restores the exchanged conjugate transpose
of the SAME physical annular amplitude, including its order factor.
Source: restoration after `new:eq:carrier-ibp`. -/
theorem modifiedAmplitude_initial_adjoint_annular_eq
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (f : (E × P) → CarrierVariables (d + 1) → ℝ)
    (w₀ : E × P → CarrierVariables (d + 1))
    (a : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) (param : P) :
    modifiedAmplitude lam p (normalizedTermAmplitude basis f w₀
      (normalizedAdjointAnnularElapsedAmplitude a χout χsource β π elapsed lam p)
      initialJointTransferTerm param) =
      fun x z ξ => (annularElapsedAmplitude a χout χsource β π elapsed lam z x ξ).conjTranspose := by
  funext x z ξ
  simp only [modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
    Pi.smul_apply, normalizedTermAmplitude, matrixSlice, initialJointTransferTerm,
    IsometricEmbedding.Response.NearCarrier.AmplitudeExpression.evaluate,
    jointAmplitudeFields, normalizedSlice, normalizedAdjointAnnularElapsedAmplitude,
    smul_smul, mul_inv_cancel₀ (zpow_ne_zero p hlam), one_smul,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, mul_inv_cancel₀ hlam]

/-- The initial reverse branch is exactly `annularEnvelopeOperator.adjoint`.
This is an identity of the published operators, using the literal reversed
carrier phase and complete original amplitude; no transport adjoint is used.
Source: the adjoint case of `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseAnnularBranchOperator_initial_eq_adjoint
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    (param : P) (hφ : Continuous (fun x => φ x param)) :
    reverseAnnularBranchOperator basis Ψ elapsed lam p φ w₀
      (normalizedAdjointAnnularElapsedAmplitude a χout χsource β π elapsed lam p)
      initialJointTransferTerm param hφ =
      (annularEnvelopeOperator Ψ a χout χsource β π elapsed lam
        (fun x => φ x param) hφ).adjoint := by
  rw [annularEnvelopeOperator_adjoint]
  unfold reverseAnnularBranchOperator
  rw [modifiedAmplitude_initial_adjoint_annular_eq basis _ w₀ a χout χsource β π
    elapsed hlam p param]
  simp only [Matrix.conjTranspose_conjTranspose]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
