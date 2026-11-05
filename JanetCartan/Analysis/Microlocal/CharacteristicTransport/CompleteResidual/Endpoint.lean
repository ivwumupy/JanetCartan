module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation

/-!
# The endpoint as the original spacetime PDO

The upper endpoint of the retarded integral is a spatial PDO after the
original right multiplier. For `app:ch_regular_base:eq:energy-complete-residual`,
combine their literal Fourier integrals into the spacetime symbol
A_t W(t,t) β, with the same compact frequency regularization. This retains
the physical normalization and the original source-masked datum.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The entire time-coefficient-weighted endpoint is a spacetime PDO with
the original right multiplier β. Taking b = W₀ + W₁ retains the endpoint
correction A_t W₁(t,t) β. The source mask is already in v, and no multiplier
or mask changes position (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem timeCoefficient_cutFixedTimeFourier_diagonal_eq_spacetimePDO
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E FV) (M : E → Mat) (x : E)
    (hdiag : ∀ t y η, Ψ t t y η = inner ℝ y η)
    (hb : Continuous (b (x 0) (x 0) (spatialPart x)))
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    (M x).mulVec (cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)) =
      graphOperator (fun z ξ ↦ inner ℝ z ξ)
        (fun z _ ξ ↦ (θ ξ * β ξ) •
          (M z * b (z 0) (z 0) (spatialPart z) (spatialPart ξ))) v x := by
  have hΨ : Continuous (Ψ (x 0) (x 0) (spatialPart x)) := by
    have he : Ψ (x 0) (x 0) (spatialPart x) =
        fun η ↦ inner ℝ (spatialPart x) η := funext fun η ↦ hdiag _ _ η
    rw [he]
    exact (innerSL ℝ (spatialPart x)).continuous
  have hi := integrable_cutFixedTimeFourierIntegrand Ψ b β θ v
    (x 0) (x 0) (spatialPart x) hΨ hb hβ hθ hθcs
  have hmap := (sourceMatrixAction (M x)).integral_comp_comm hi
  change (∫ ξ, (M x).mulVec
      (cutFixedTimeFourierIntegrand Ψ b β θ v (x 0) (x 0) (spatialPart x) ξ)) =
    (M x).mulVec (∫ ξ, cutFixedTimeFourierIntegrand Ψ b β θ v
      (x 0) (x 0) (spatialPart x) ξ) at hmap
  rw [← integral_cutFixedTimeFourier Ψ b β θ v (x 0) (x 0) (spatialPart x)
    hΨ hb hβ hθ hθcs, Matrix.mulVec_smul, ← hmap,
    graphOperator_eq_sourceFourierIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  have he : Complex.exp (Complex.I * ((x 0 * ξ 0 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (inner ℝ (spatialPart x) (spatialPart ξ) : ℂ)) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
    rw [← Complex.exp_add, inner_eq_time_add_spatial]
    congr 1
    push_cast
    ring
  simp only [cutFixedTimeFourierIntegrand, hdiag, Matrix.mulVec_smul,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, smul_smul]
  rw [← mul_assoc, he]

end JanetCartan.CharacteristicTransport.CompleteResidual
