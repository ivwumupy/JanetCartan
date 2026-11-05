module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.PhysicalModulation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale

/-!
# Ordered envelope estimates in the original physical coordinates

The selected characteristic operator and its datum use one fixed coordinate
permutation. Undoing this permutation commutes with every parameter derivative
and preserves the exact Fourier Sobolev norm. This transfers the selected
history envelope to a literal physical residual letter, before the finite sum.
Consumer: `app:ch_response:eq:fixed-factor-transfer` in the measured word proof.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution.AnnularSobolev
open RegularSector.FiniteEvolution RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.ResidualCoordinates

variable {d r : ℕ} {I Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean (d+1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

private theorem orderedParameterWord_equiv (e : H ≃L[ℝ] H)
    (ps : List Par) (u : Par → H) :
    orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps (fun c ↦ e (u c)) =
      fun c ↦ e (orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps u c) := by
  induction ps with
  | nil => rfl
  | cons v ps ih =>
    simp only [orderedTransferAction, ih]
    funext c
    exact congrArg (fun D : Par →L[ℝ] H ↦ D v) e.comp_fderiv

/-- Every ordered mixed parameter estimate for the actual selected chart
operator is the estimate for its original physical conjugate with identical
constant, source and phase. This uses no regularity of the parameter-indexed
L² family beyond what was already needed to prove its chart envelope
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem physical_operator_ordered_envelope_of_chart
    (index : Fin (d+1)) (T : I → H →L[ℂ] H) (ρ A K : I → ℝ)
    (φ : I → Par → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (u : I → Par → H) (V : Set Par) (ps : List Par)
    (hchart : HasEnvelopeProfile vectorFourierSobolevScale
      (fun q : I × V ↦ orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
        (fun c ↦ demodulatedL2Operator (ρ q.1) (φ q.1 c ∘ physicalCoordinates index)
          ((hφ q.1 c).comp (physicalCoordinates index).continuous) (T q.1)
          (physicalPullbackL2 index (u q.1 c))) q.2)
      (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) :
    HasEnvelopeProfile vectorFourierSobolevScale
      (fun q : I × V ↦ orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
        (fun c ↦ demodulatedL2Operator (ρ q.1) (φ q.1 c) (hφ q.1 c)
          (physicalOperator index (T q.1)) (u q.1 c)) q.2)
      (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  let e : H ≃L[ℝ] H :=
    (physicalPullbackL2 index).symm.toContinuousLinearEquiv.restrictScalars ℝ
  let v : I → Par → H := fun i c ↦ demodulatedL2Operator (ρ i)
    (φ i c ∘ physicalCoordinates index)
    ((hφ i c).comp (physicalCoordinates index).continuous) (T i)
    (physicalPullbackL2 index (u i c))
  have he i : (fun c ↦ demodulatedL2Operator (ρ i) (φ i c) (hφ i c)
      (physicalOperator index (T i)) (u i c)) = fun c ↦ e (v i c) := by
    funext c
    rw [demodulatedL2Operator_physicalOperator, physicalOperator_apply]
    rfl
  intro s
  obtain ⟨C,hC,hbound⟩ := hchart s
  refine ⟨C,hC,?_⟩
  intro q
  dsimp only
  rw [he, orderedParameterWord_equiv]
  obtain ⟨hm,hb⟩ := hbound q
  change MemVectorFourierSobolev (s : ℝ)
    (orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps (v q.1) q.2) at hm
  change MemVectorFourierSobolev (s : ℝ)
    ((physicalPullbackL2 index).symm
      (orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps (v q.1) q.2)) ∧ _
  have hout := (memVectorFourierSobolev_physicalPullbackL2_symm index (s : ℝ) _).mpr hm
  refine ⟨hout,?_⟩
  change vectorFourierSobolevScale.gradeNorm s
    ((physicalPullbackL2 index).symm
      (orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps (v q.1) q.2)) ≤ _
  rw [vectorFourierSobolevScale_gradeNorm s hout,
    vectorFourierSobolevNorm_physicalPullbackL2_symm]
  rw [vectorFourierSobolevScale_gradeNorm s hm] at hb
  exact hb

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
