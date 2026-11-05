module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation

/-!
# The same annular envelope operator and its literal branches

Shared objects for the weak derivative and quantitative Sobolev deductions of
`app:ch_response:eq:direct-envelope-profile`. The physical operator, frequency,
elapsed time, masks and beta/high-pass are fixed while the carrier parameter
varies. No estimate or transfer identity is stored in these definitions.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral FourierIntegral.FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual annular envelope of the fixed elapsed graph, for
`app:ch_response:eq:direct-envelope-profile`. -/
def annularEnvelopeOperator (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed lam : ℝ)
    (φ : E → ℝ) (hφ : Continuous φ) : H →L[ℂ] H :=
  demodulatedL2Operator lam φ hφ
    (fullGraphOperator (elapsedPhase Ψ elapsed)
      (annularElapsedAmplitude a χout χsource β π elapsed lam))

/-- The realized branch acts on the actual `originalDatumDerivative` in the
compact expansion, with the unchanged original elapsed phase.
Source: restoration after `new:eq:carrier-ibp`. -/
def annularBranchOperator (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed lam : ℝ) (p : ℤ) (φ : E → P → ℝ)
    (w₀ : E × P → CarrierVariables (d + 1))
    (α : (E × P) → CarrierVariables (d + 1) → Mat)
    (branch : JointTransferTerm (d + 1) P Mat ι) (param : P)
    (hφ : Continuous (fun x => φ x param)) : H →L[ℂ] H :=
  demodulatedL2Operator lam (fun x => φ x param) hφ
    (fullGraphOperator (elapsedPhase Ψ elapsed)
      (modifiedAmplitude lam p
        (normalizedTermAmplitude basis (elapsedCarrierPhase Ψ elapsed φ) w₀ α branch param)))

/-- The branch for the literal reversed carrier phase. The forward graph's
amplitude exchanges positions and conjugate-transposes the COMPLETE restored
branch before taking its Hilbert adjoint. This is precisely the kernel in
`demodulated_reverseBranchGraphOperator_eq_normalized`; it introduces no
transport-adjoint substitution (`new:eq:carrier-ibp`). -/
def reverseAnnularBranchOperator
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed lam : ℝ) (p : ℤ) (φ : E → P → ℝ)
    (w₀ : E × P → CarrierVariables (d + 1))
    (α : (E × P) → CarrierVariables (d + 1) → Mat)
    (branch : JointTransferTerm (d + 1) P Mat ι) (param : P)
    (hφ : Continuous (fun x => φ x param)) : H →L[ℂ] H :=
  let A := modifiedAmplitude lam p
    (normalizedTermAmplitude basis (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ)
      w₀ α branch param)
  demodulatedL2Operator lam (fun x => φ x param) hφ
    (fullGraphOperator (elapsedPhase Ψ elapsed) (fun x z ξ => (A z x ξ).conjTranspose)).adjoint

/-- The undifferentiated realized branch equals the SAME annular envelope
operator. This identifies the base case of the weak derivative induction;
no operator equality is assumed (`new:eq:carrier-ibp`). -/
theorem annularBranchOperator_initial_eq
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed : ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    (param : P) (hφ : Continuous (fun x => φ x param)) :
    annularBranchOperator basis Ψ elapsed lam p φ w₀
      (normalizedAnnularElapsedAmplitude a χout χsource β π elapsed lam p)
      initialJointTransferTerm param hφ =
      annularEnvelopeOperator Ψ a χout χsource β π elapsed lam (fun x => φ x param) hφ := by
  unfold annularBranchOperator annularEnvelopeOperator
  rw [modifiedAmplitude_initial_annular_eq basis _ w₀ a χout χsource β π elapsed hlam p param]

/-- The literal adjoint of the annular envelope uses the same physical
graph's Hilbert adjoint and the same carrier conjugation. Source: the
reversed-phase case of `app:ch_response:eq:direct-envelope-profile`. -/
theorem annularEnvelopeOperator_adjoint (Ψ : TwoTimePhase d) (a : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed lam : ℝ)
    (φ : E → ℝ) (hφ : Continuous φ) :
    (annularEnvelopeOperator Ψ a χout χsource β π elapsed lam φ hφ).adjoint =
      demodulatedL2Operator lam φ hφ
        (fullGraphOperator (elapsedPhase Ψ elapsed)
          (annularElapsedAmplitude a χout χsource β π elapsed lam)).adjoint :=
  demodulatedL2Operator_adjoint lam φ hφ _

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
