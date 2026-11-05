module
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.SymbolProfiles
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.MaskedBudgets
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# Exact normal certificates for the complete elliptic response

The full elliptic symbol can absorb its literal output mask while retaining
the same bounded PDO. The original selected low coefficient admission produces
its normal certificate; no response or complementary estimate is a premise.
Consumer: complete frequency integration for the actual normalized solver and
residual in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open RegularSector RegularSector.FiniteMasks.ActualFamily EllipticComplement EllipticLocalization
open Characteristic.PdoRealization CharacteristicTransport.CompleteResidual FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Output absorption is equality of the complete bounded operators,
including every physical frequency (`app:ch_response:eq:direct-envelope-profile`). -/
theorem maskedPhysicalPDO_inputMask_output_absorption
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (χout : E → ℂ) (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (a : E → E → CMat) :
    maskedPhysicalPDO (fun y ↦ (f.inputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ))
      (fun y ξ ↦ χout y • a y ξ) =
    maskedPhysicalPDO χout (fun z ↦ (f.inputMask z : ℂ)) a := by
  unfold maskedPhysicalPDO
  congr 1
  funext y z ξ
  exact inputMask_mul_masked_elliptic_amplitude f χout hos a y z ξ

/-- The original low coefficient bounds certify the exact absorbed full
inverse and residual symbols, uniformly before threshold and coefficients.
These certificates supply the full-frequency strong limits used in
`completeDiagonalAnnularComplement_sobolev`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_complete_elliptic_absorbed_normal_certificates
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius)) :
    ∃ R > 0, ∃ N > 0,
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
        cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ residual : Bool,
        GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol
          (fun y ↦ (f.inputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ))
          (fun y ξ ↦ χout y • (if residual then ellipticResidualSymbol f hK threshold Q B y ξ
            else ellipticInverseSymbol f hK threshold Q y ξ))) R N := by
  obtain ⟨R,hR,N,hN,_,_,hcert⟩ :=
    exists_elliptic_masked_pdo_budgets f hK hΩ hRQΩ χout ho hoc hos
  refine ⟨R,hR,N,hN,?_⟩
  intro threshold ht Q B hQ hB hmap hQl hBl residual
  let a := fun y ξ ↦ if residual then ellipticResidualSymbol f hK threshold Q B y ξ
    else ellipticInverseSymbol f hK threshold Q y ξ
  have hamem : a ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)) := by
    cases residual <;> simp [a]
  have hc := (hcert threshold ht Q B hQ hB hmap hQl hBl a hamem).1
  have he : (fun y z ξ ↦ ((f.inputMask y : ℂ) * (f.inputMask z : ℂ)) •
      (χout y • a y ξ)) = fun y z ξ ↦ (χout y * (f.inputMask z : ℂ)) • a y ξ := by
    funext y z ξ
    exact inputMask_mul_masked_elliptic_amplitude f χout hos a y z ξ
  change GraphNormalAmplitudeBounds (physicalPDOCycleSymbol _) R N
  rw [he]
  exact hc

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
