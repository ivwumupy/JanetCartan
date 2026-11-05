module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# The original physical PDO inside the full-amplitude branch calculus

The elapsed branch API accepts an arbitrary full amplitude. Its diagonal
phase can therefore represent the physical PDO while the original symbol
keeps all frequency components. Restoring its initial normalized amplitude
identifies the same masked operator and its literal Hilbert adjoint. No
boundedness or response-preservation estimate is inserted as a premise.

Sources: `app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution DirectEvolution.CompactTransfer DirectEvolution.BranchAmplitudes
open DirectEvolution.ModifiedLow DirectEvolution.AnnularSobolev FourierIntegral
open RegularSector.Characteristic.EvolutionIntegral
open CharacteristicTransport.CompleteResidual
variable {d r : ℕ} {ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Restoring the initial branch of the full-frequency PDO amplitude gives
exactly its original amplitude. The whole symbol, source mask and Fourier
multipliers stay inside the frequency normalization; the independent full
source parameter is fixed (`new:eq:carrier-ibp`). -/
theorem modifiedAmplitude_initial_fullAmplitude_eq
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d+1)))
    (f : (E × Param) → CarrierVariables (d+1) → ℝ)
    (w₀ : E × Param → CarrierVariables (d+1))
    (A : FullAmplitude (d+1) r) {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) (param : Param) :
    modifiedAmplitude lam p (normalizedTermAmplitude basis f w₀
      (fun q w ↦ (lam ^ p)⁻¹ • normalizedFullAmplitude A lam (q.1, w.fst, w.snd))
      initialJointTransferTerm param) = A := by
  funext x z ξ
  simp only [modifiedAmplitude, NearCarrierSymbol.physicalAmplitudeOfNormalized,
    Pi.smul_apply, normalizedTermAmplitude, matrixSlice, initialJointTransferTerm,
    IsometricEmbedding.Response.NearCarrier.AmplitudeExpression.evaluate,
    jointAmplitudeFields, normalizedSlice, normalizedFullAmplitude,
    smul_smul, mul_inv_cancel₀ (zpow_ne_zero p hlam), one_smul,
    WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, mul_inv_cancel₀ hlam]

/-- The lower full-amplitude branch calculus applies to the literal masked
PDO. Only its phase is written in zero-elapsed coordinates; the full-frequency
symbol is preserved without converting it to a two-time spatial amplitude.
This identifies the original elliptic solver/residual branch before its
quantitative envelope application (`app:ch_response:eq:direct-envelope-profile`). -/
theorem annularBranchOperator_initial_maskedPDO
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d+1)))
    (φ : E → Param → ℝ) (w₀ : E × Param → CarrierVariables (d+1))
    (symbol : E → E → Mat) (χout χsource : E → ℂ)
    {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) (param : Param)
    (hφ : Continuous (fun x ↦ φ x param)) :
    annularBranchOperator basis (fun _ _ x ξ ↦ inner ℝ x ξ) 0 lam p φ w₀
      (fun q w ↦ (lam ^ p)⁻¹ • normalizedFullAmplitude
        (fun x z ξ ↦ (χout x * χsource z) • symbol x ξ) lam (q.1, w.fst, w.snd))
      initialJointTransferTerm param hφ =
    demodulatedL2Operator lam (fun x ↦ φ x param) hφ
      (maskedPhysicalPDO χout χsource symbol) := by
  unfold annularBranchOperator
  rw [modifiedAmplitude_initial_fullAmplitude_eq basis _ w₀ _ hlam p param]
  have hphase : elapsedPhase (fun (_ _ : ℝ) (x ξ : Euclidean d) ↦ inner ℝ x ξ) 0 =
      (fun x ξ : E ↦ inner ℝ x ξ) := by
    funext x ξ
    exact elapsedPhase_zero _ (fun _ _ _ ↦ rfl) x ξ
  rw [hphase]
  rfl

/-- The reversed initial full-amplitude branch is the Hilbert adjoint of the
same masked physical PDO. Both physical positions and the entire matrix
symbol are exchanged and conjugate-transposed exactly once in the carrier
amplitude (`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem reverseAnnularBranchOperator_initial_maskedPDO
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d+1)))
    (φ : E → Param → ℝ) (w₀ : E × Param → CarrierVariables (d+1))
    (symbol : E → E → Mat) (χout χsource : E → ℂ)
    {lam : ℝ} (hlam : lam ≠ 0) (p : ℤ) (param : Param)
    (hφ : Continuous (fun x ↦ φ x param)) :
    reverseAnnularBranchOperator basis (fun _ _ x ξ ↦ inner ℝ x ξ) 0 lam p φ w₀
      (fun q w ↦ (lam ^ p)⁻¹ • normalizedFullAmplitude
        (fun x z ξ ↦ ((χout z * χsource x) • symbol z ξ).conjTranspose)
        lam (q.1, w.fst, w.snd)) initialJointTransferTerm param hφ =
    demodulatedL2Operator lam (fun x ↦ φ x param) hφ
      (maskedPhysicalPDO χout χsource symbol).adjoint := by
  unfold reverseAnnularBranchOperator
  rw [modifiedAmplitude_initial_fullAmplitude_eq basis _ w₀ _ hlam p param]
  have hphase : elapsedPhase (fun (_ _ : ℝ) (x ξ : Euclidean d) ↦ inner ℝ x ξ) 0 =
      (fun x ξ : E ↦ inner ℝ x ξ) := by
    funext x ξ
    exact elapsedPhase_zero _ (fun _ _ _ ↦ rfl) x ξ
  rw [hphase]
  simp only [Matrix.conjTranspose_conjTranspose]
  rfl

end JanetCartan.ResponseTransfer.DiagonalPdo
