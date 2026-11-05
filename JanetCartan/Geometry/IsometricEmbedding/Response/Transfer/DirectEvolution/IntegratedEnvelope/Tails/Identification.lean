module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.OperatorIdentification

/-!
# Identifying the integrated tail with the original elapsed operator

These are exact identities for the integrals returned by
`originalAnnularComplement_elapsed_sobolev`. The near part is the one in
`IntegratedEnvelope.Basic`, with its original beta multiplied by the annular
selector. The bounded realizations are the original strong integral and the
operator supplied by `IntegratedEnvelope.Construction`; no new physical
operator is substituted. Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open AnnularSobolev AnnularComplement
open JanetCartan.ResponseTransfer.Complement
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d r

/-- The literal adjoint of the annular envelope has exactly the adjoint
elapsed integral with the same beta and cutoff. All exchanged factor order
is inherited from the actual Hilbert adjoint.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularEnvelopeAdjointIntegral_eq_elapsedGraphAdjointIntegral
    (Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    annularEnvelopeAdjointIntegral Δ Ψ b χout χsource β π lam φ hφ u =
      carrierMultiplication (-lam) φ hφ
        (∫ t in Icc 0 Δ, (elapsedGraph Ψ b χout χsource
          (fun ξ => π (lam⁻¹ • ξ) * β ξ) t).adjoint
            (carrierMultiplication lam φ hφ u)) := by
  simp only [annularEnvelopeAdjointIntegral, annularEnvelopeOperator_adjoint,
    demodulatedL2Operator, ContinuousLinearMap.comp_apply,
    annularElapsedAmplitude_eq_elapsedAmplitude, elapsedGraph]
  exact (carrierMultiplication (-lam) φ hφ).integral_comp_comm'
    (AddMonoidHomClass.isometry_of_norm _
      (norm_carrierMultiplication_apply (-lam) φ hφ)).antilipschitzWith _

/-- The complete physical difference, after literal demodulation, is the
original uncut integral minus the annular integral already published in
`IntegratedEnvelope.Basic`, in either orientation. The identity is valid for
the actual integrals; integrability is proved separately by the primitive
tail theorem. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem demodulatedElapsedDifference_eq_annularDifference
    (adj : Bool) (Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    carrierMultiplication (-lam) φ hφ
      ((∫ t in Icc 0 Δ, annularGraphOrientation adj
        (elapsedGraph Ψ b χout χsource β t) (carrierMultiplication lam φ hφ u)) -
       (∫ t in Icc 0 Δ, annularGraphOrientation adj
        (elapsedGraph Ψ b χout χsource (fun ξ => π (lam⁻¹ • ξ) * β ξ) t)
          (carrierMultiplication lam φ hφ u))) =
      carrierMultiplication (-lam) φ hφ
        (∫ t in Icc 0 Δ, annularGraphOrientation adj
          (elapsedGraph Ψ b χout χsource β t) (carrierMultiplication lam φ hφ u)) -
      (if adj then annularEnvelopeAdjointIntegral Δ Ψ b χout χsource β π lam φ hφ u
       else annularEnvelopeIntegral Δ Ψ b χout χsource β π lam φ hφ u) := by
  rw [map_sub]
  congr 1
  cases adj
  · exact (annularEnvelopeIntegral_eq_elapsedGraphIntegral
      Δ Ψ b χout χsource β π lam φ hφ u).symm
  · exact (annularEnvelopeAdjointIntegral_eq_elapsedGraphAdjointIntegral
      Δ Ψ b χout χsource β π lam φ hφ u).symm

/-- Interpretation of the same integrated difference using the actual
bounded realizations, including the literal adjoint of their difference.
The four action identities are supplied by `strongIntegral_apply`,
`strongIntegral_adjoint_apply` and `IntegratedEnvelope.Construction`.
No remainder bound or remainder realization is a hypothesis.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem demodulatedElapsedDifference_eq_boundedDifference
    (adj : Bool) (Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (Tfull Tannular : H →L[ℂ] H)
    (hfull : ∀ v, Tfull v = elapsedGraphIntegral Δ Ψ b χout χsource β v)
    (hfullAdj : ∀ v, Tfull.adjoint v =
      ∫ t in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β t).adjoint v)
    (hnear : ∀ v, Tannular v = annularEnvelopeIntegral Δ Ψ b χout χsource β π lam φ hφ v)
    (hnearAdj : ∀ v, Tannular.adjoint v =
      annularEnvelopeAdjointIntegral Δ Ψ b χout χsource β π lam φ hφ v) (u : H) :
    carrierMultiplication (-lam) φ hφ
      ((∫ t in Icc 0 Δ, annularGraphOrientation adj
        (elapsedGraph Ψ b χout χsource β t) (carrierMultiplication lam φ hφ u)) -
       (∫ t in Icc 0 Δ, annularGraphOrientation adj
        (elapsedGraph Ψ b χout χsource (fun ξ => π (lam⁻¹ • ξ) * β ξ) t)
          (carrierMultiplication lam φ hφ u))) =
      annularGraphOrientation adj (demodulatedL2Operator lam φ hφ Tfull - Tannular) u := by
  rw [demodulatedElapsedDifference_eq_annularDifference]
  cases adj
  · change carrierMultiplication (-lam) φ hφ
        (elapsedGraphIntegral Δ Ψ b χout χsource β (carrierMultiplication lam φ hφ u)) -
        annularEnvelopeIntegral Δ Ψ b χout χsource β π lam φ hφ u = _
    rw [← hfull (carrierMultiplication lam φ hφ u), ← hnear u]
    rfl
  · change carrierMultiplication (-lam) φ hφ
        (∫ t in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β t).adjoint
          (carrierMultiplication lam φ hφ u)) -
        annularEnvelopeAdjointIntegral Δ Ψ b χout χsource β π lam φ hφ u = _
    rw [← hfullAdj (carrierMultiplication lam φ hφ u), ← hnearAdj u]
    simp only [annularGraphOrientation, ↓reduceIte, map_sub, sub_apply]
    rw [demodulatedL2Operator_adjoint]
    rfl

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Tails
