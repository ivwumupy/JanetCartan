module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.BranchAmplitudes.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Assembly
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Joint integrals of the same annular branches

The compact expansion of `paper-v2.tex`, `new:eq:carrier-ibp`, uses Lebesgue
measure on `CarrierVariables`. The graph kernels use source-first iterated
integrals. This file identifies them, including `(2π)⁻ⁿ`, the Jacobian `λⁿ`,
and the amplitude order `λᵖ`. The reversed phase keeps the exchanged,
conjugate-transposed full amplitude. The consumer is the weak transfer step
in `paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open FourierIntegral CompactTransfer BranchAmplitudes ModifiedLow
variable {n r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "V" => Fin r → ℂ

/-- The literal normalized joint integral for one transfer branch, acting on
actual derivatives of the original datum. All physical normalization factors
are retained (`new:eq:carrier-ibp`). -/
def normalizedBranchIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (f : (E × P) → CarrierVariables n → ℝ) (w₀ : E × P → CarrierVariables n)
    (α : (E × P) → CarrierVariables n → Mat) (a : E × P → V)
    (t : JointTransferTerm n P Mat ι) (lam : ℝ) (p : ℤ) (q : E × P) : V :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ • (lam ^ n • (lam ^ p •
    ∫ w, oscillation f lam q w •
      jointTransferTermValue b ReverseDerivative.matrixAction f w₀ α a t q w))

/-- Lebesgue measure on the Hilbert product introduces no extra constant.
Fubini is justified by integrability of the actual joint integrand, and retains
the source-first order used by `graphOperator` (`new:eq:carrier-ibp`). -/
theorem integral_carrierVariables_eq_sourceFirst {g : CarrierVariables n → V}
    (hg : Integrable g) :
    (∫ w, g w) = ∫ θ : E, ∫ z : E, g (WithLp.toLp 2 (z, θ)) := by
  have hi := (WithLp.volume_preserving_toLp E E).integrable_comp hg.aestronglyMeasurable
  have he := (WithLp.volume_preserving_toLp E E).integral_comp
    (MeasurableEquiv.toLp 2 (E × E)).measurableEmbedding g
  rw [← he]
  exact integral_prod_symm _ (hi.mpr hg)

/-- The restored forward graph branch equals its normalized joint integral.
This is the exact kernel identification needed before weak differentiation;
the datum is `originalDatumDerivative t.datumWord a`, not a new envelope.
Source: restoration following `new:eq:carrier-ibp`. -/
theorem demodulated_branchGraphOperator_eq_jointIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (Θ : E → E → ℝ) (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables n)
    (α : (E × P) → CarrierVariables n → Mat) (a : E × P → V)
    (t : JointTransferTerm n P Mat ι) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (q : E × P)
    (hΘ : ∀ z θ, modifiedAmplitude lam p
      (normalizedTermAmplitude b (carrierPhase Θ φ) w₀ α t q.2) q.1 z (lam • θ) ≠ 0 →
      Θ q.1 (lam • θ) = lam * Θ q.1 θ)
    (hi : Integrable (fun w => oscillation (carrierPhase Θ φ) lam q w •
      jointTransferTermValue b ReverseDerivative.matrixAction
        (carrierPhase Θ φ) w₀ α a t q w)) :
    carrier (-lam) (fun y => φ y q.2) q.1 •
      graphOperator Θ (modifiedAmplitude lam p
        (normalizedTermAmplitude b (carrierPhase Θ φ) w₀ α t q.2))
        (fun z => carrier lam (fun y => φ y q.2) z •
          originalDatumDerivative t.datumWord a (z, q.2)) q.1 =
      normalizedBranchIntegral b (carrierPhase Θ φ) w₀ α a t lam p q := by
  rw [demodulated_branchGraphOperator_eq_normalized b Θ φ w₀ α t q.2 _ hlam p q.1 hΘ]
  unfold normalizedBranchIntegral
  rw [integral_carrierVariables_eq_sourceFirst hi]
  simp only [jointTransferTermValue, ReverseDerivative.matrixAction,
    sourceDatum, WithLp.fst, Matrix.smul_mulVec,
    smul_comm (oscillation _ _ _ _) (lam ^ p), integral_smul]
  rfl

/-- The literal reversed graph branch equals the same joint integral for the
reversed carrier phase. In the physical forward graph the amplitude is
`fun x z ξ => (A z x ξ).conjTranspose`; its Hilbert adjoint has the displayed
kernel. No transport-adjoint replacement is made (`new:eq:carrier-ibp`). -/
theorem demodulated_reverseBranchGraphOperator_eq_jointIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (Θ : E → E → ℝ) (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables n)
    (α : (E × P) → CarrierVariables n → Mat) (a : E × P → V)
    (t : JointTransferTerm n P Mat ι) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (q : E × P)
    (hΘ : ∀ z θ, modifiedAmplitude lam p
      (normalizedTermAmplitude b (adjointCarrierPhase Θ φ) w₀ α t q.2) q.1 z (lam • θ) ≠ 0 →
      Θ z (lam • θ) = lam * Θ z θ)
    (hi : Integrable (fun w => oscillation (adjointCarrierPhase Θ φ) lam q w •
      jointTransferTermValue b ReverseDerivative.matrixAction
        (adjointCarrierPhase Θ φ) w₀ α a t q w)) :
    carrier (-lam) (fun y => φ y q.2) q.1 •
      reverseGraphOperator Θ (fun y z ξ => modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase Θ φ) w₀ α t q.2) z y ξ)
        (fun z => carrier lam (fun y => φ y q.2) z •
          originalDatumDerivative t.datumWord a (z, q.2)) q.1 =
      normalizedBranchIntegral b (adjointCarrierPhase Θ φ) w₀ α a t lam p q := by
  rw [demodulated_reverseBranchGraphOperator_eq_normalized b Θ φ w₀ α t q.2 _ hlam p q.1 hΘ]
  unfold normalizedBranchIntegral
  rw [integral_carrierVariables_eq_sourceFirst hi]
  simp only [jointTransferTermValue, ReverseDerivative.matrixAction,
    sourceDatum, WithLp.fst, Matrix.smul_mulVec,
    smul_comm (oscillation _ _ _ _) (lam ^ p), integral_smul]
  rfl

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
