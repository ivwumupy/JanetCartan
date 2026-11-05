module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev.Fourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation

/-!
# Exact modulation through the selected physical sector sum

The existing coordinate isometries pull back the carrier and original datum
together. Demodulation therefore commutes with physical transport and the finite
sum of the same chart operators. Every signed Fourier-Sobolev norm is retained
with constant one. These identities supply the physical assembly step for both
solver and complete residual envelopes (`app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteEvolution JanetCartan.ResponseTransfer.Complement DirectEvolution.AnnularSobolev
open FourierIntegral Pseudodifferential
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- The selected physical permutation pulls back the original carrier and datum
together, with no frequency or measure change. Source: the finite-family step
of `app:ch_response:eq:fixed-factor-transfer`. -/
theorem physicalPullbackL2_carrierMultiplication
    (i : Fin (d + 1)) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    physicalPullbackL2 i (carrierMultiplication lam φ hφ u) =
      carrierMultiplication lam (φ ∘ physicalCoordinates i)
        (hφ.comp (physicalCoordinates i).continuous) (physicalPullbackL2 i u) := by
  apply Lp.ext
  have hm := (measurePreserving_physicalCoordinates i).quasiMeasurePreserving.ae_eq_comp
    (carrierMultiplication_ae lam φ hφ u)
  filter_upwards [physicalPullbackL2_coeFn i (carrierMultiplication lam φ hφ u), hm,
    carrierMultiplication_ae lam (φ ∘ physicalCoordinates i)
      (hφ.comp (physicalCoordinates i).continuous) (physicalPullbackL2 i u),
    physicalPullbackL2_coeFn i u] with y hy hm' hc hu
  simp only [Function.comp_apply] at hy hm' hu
  rw [hy, hm', hc, hu]
  rfl

/-- The inverse physical permutation restores the same carrier. It is the
literal inverse of the preceding pullback, with the original L² measure
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem physicalPullbackL2_symm_carrierMultiplication
    (i : Fin (d + 1)) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    (physicalPullbackL2 i).symm
      (carrierMultiplication lam (φ ∘ physicalCoordinates i)
        (hφ.comp (physicalCoordinates i).continuous) u) =
      carrierMultiplication lam φ hφ ((physicalPullbackL2 i).symm u) := by
  apply (physicalPullbackL2 i).injective
  rw [LinearIsometryEquiv.apply_symm_apply, physicalPullbackL2_carrierMultiplication,
    LinearIsometryEquiv.apply_symm_apply]

/-- Demodulation of a selected physical factor is exactly physical transport
of its chart demodulation. Source and output use the SAME pulled-back phase;
all internal cutoffs and the original operator are retained. Applying this to
`T.adjoint` gives the literal adjoint case
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem demodulatedL2Operator_physicalOperator
    (i : Fin (d + 1)) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (T : H →L[ℂ] H) :
    demodulatedL2Operator lam φ hφ (physicalOperator i T) =
      physicalOperator i (demodulatedL2Operator lam (φ ∘ physicalCoordinates i)
        (hφ.comp (physicalCoordinates i).continuous) T) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply, physicalOperator_apply]
  rw [physicalPullbackL2_carrierMultiplication, physicalPullbackL2_symm_carrierMultiplication]

/-- Sum the actual chart demodulations on the common physical Hilbert space.
There is one original source and one original carrier; only their literal
coordinate pullbacks vary with the chart. This identifies the finite retarded
solver/residual sum consumed by the fixed inverse
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem demodulatedL2Operator_finitePhysicalOperator
    {ι : Type*} [Fintype ι] (index : ι → Fin (d + 1)) (T : ι → H →L[ℂ] H)
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) :
    demodulatedL2Operator lam φ hφ (finitePhysicalOperator index T) =
      finitePhysicalOperator index (fun p ↦ demodulatedL2Operator lam
        (φ ∘ physicalCoordinates (index p)) (hφ.comp (physicalCoordinates (index p)).continuous)
        (T p)) := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  simp only [finitePhysicalOperator, demodulatedL2Operator, ContinuousLinearMap.comp_apply,
    sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact DFunLike.congr_fun (demodulatedL2Operator_physicalOperator (index p) lam φ hφ (T p)) u

/-- Physical transport preserves exactly every signed Sobolev norm of the
same demodulated response, including negative orders. The original source is
pulled back along with its phase, so no comparison constant is introduced
(`app:ch_response:eq:fixed-factor-transfer`, `app:ch_regular_base:eq:negative-duality`). -/
theorem demodulated_physicalOperator_sobolev
    (i : Fin (d + 1)) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (T : H →L[ℂ] H) (s : ℝ) (u : H) :
    let v := demodulatedL2Operator lam (φ ∘ physicalCoordinates i)
      (hφ.comp (physicalCoordinates i).continuous) T (physicalPullbackL2 i u)
    (MemVectorFourierSobolev s (demodulatedL2Operator lam φ hφ (physicalOperator i T) u) ↔
      MemVectorFourierSobolev s v) ∧
    vectorFourierSobolevNorm s (demodulatedL2Operator lam φ hφ (physicalOperator i T) u) =
      vectorFourierSobolevNorm s v := by
  dsimp only
  rw [demodulatedL2Operator_physicalOperator, physicalOperator_apply]
  exact ⟨memVectorFourierSobolev_physicalPullbackL2_symm i s _,
    vectorFourierSobolevNorm_physicalPullbackL2_symm i s _⟩

end JanetCartan.ResponseTransfer.RetainedFactors
