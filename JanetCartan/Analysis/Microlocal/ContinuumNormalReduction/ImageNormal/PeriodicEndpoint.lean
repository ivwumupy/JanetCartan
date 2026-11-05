module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint.Vector
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.NegativeDual

/-!
# Transferring the adjoint endpoint and negative Sobolev estimate

For `app:ch_background:prop:bg-frame`, Step 1, a real Euclidean operator whose
literal adjoint has compact chart support and an L²-to-Fourier-H¹ bound induces
a periodic adjoint with values in the actual `PeriodicSobolevSpace`. Duality
then gives the negative-Sobolev error bound for the transferred operator.

The Euclidean inputs are to be supplied by
`CoefficientRemainder.coefficientRemainderOperator_sobolev_one_bounds`,
`LocalComparison.RealSmoothing`, and the commutator realization in the parent
image-normal construction. They remain explicit here. No periodic endpoint or
negative estimate is assumed, and no measures are identified.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint

variable {n m : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin m)

/-- The literal transferred adjoint has periodic H¹ values with the Euclidean
endpoint constant times the explicit chart constant. The source restriction
is the actual isometry into Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem transferOperator_adjoint_h1_bound {r C : ℝ} (hr : r < 1 / 2)
    (T : EuclideanL2 n V →L[ℝ] EuclideanL2 n V)
    (hs : ∀ g, ∀ᵐ x ∂volume, x ∉ chartBox r → T.adjoint g x = 0)
    (hT : ∀ g, MemVectorFourierSobolev 1 (l2ComplexInclusion volume (T.adjoint g)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (T.adjoint g)) ≤ C * ‖g‖)
    (g : PeriodicL2 n V) :
    ∃ U : PeriodicSobolevSpace n V 1,
      PeriodicSobolevSpace.toL2 1 U = (transferOperator T).adjoint g ∧
      ‖U‖ ≤ (((m : ℝ) * (1 + 2 * Real.pi * n)) * C) * ‖g‖ := by
  obtain ⟨U, hU, hb⟩ := exists_real_vector_periodic_h1 hr
    (T.adjoint (toEuclidean (𝕜 := ℝ) g)) (hs _) (hT _).1
  refine ⟨U, ?_, hb.trans ?_⟩
  · rw [transferOperator_adjoint]
    exact hU
  · calc
      _ ≤ ((m : ℝ) * (1 + 2 * Real.pi * n)) *
          (C * ‖toEuclidean (𝕜 := ℝ) g‖) :=
        mul_le_mul_of_nonneg_left (hT _).2 (by positivity)
      _ = _ := by rw [toEuclidean.norm_map]; ring

/-- The H¹-valued adjoint is a genuine bounded linear map, compatible with
the literal L² adjoint. Its membership and bound are deductions from the
Euclidean support and endpoint, for `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_transferOperator_adjoint_h1 {r C : ℝ} (hr : r < 1 / 2) (hC : 0 ≤ C)
    (T : EuclideanL2 n V →L[ℝ] EuclideanL2 n V)
    (hs : ∀ g, ∀ᵐ x ∂volume, x ∉ chartBox r → T.adjoint g x = 0)
    (hT : ∀ g, MemVectorFourierSobolev 1 (l2ComplexInclusion volume (T.adjoint g)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (T.adjoint g)) ≤ C * ‖g‖) :
    ∃ A : PeriodicL2 n V →L[ℝ] PeriodicSobolevSpace n V 1,
      (PeriodicSobolevSpace.toL2 1).comp A = (transferOperator T).adjoint ∧
      ‖A‖ ≤ ((m : ℝ) * (1 + 2 * Real.pi * n)) * C := by
  choose U hU hb using transferOperator_adjoint_h1_bound hr T hs hT
  let A : PeriodicL2 n V →ₗ[ℝ] PeriodicSobolevSpace n V 1 :=
    { toFun := U
      map_add' := fun f g ↦ (PeriodicSobolevSpace.toL2_injective 1) (by
        simp only [hU, map_add])
      map_smul' := fun c f ↦ (PeriodicSobolevSpace.toL2_injective 1) (by
        simp only [hU, map_smul, RingHom.id_apply]) }
  let B := A.mkContinuous (((m : ℝ) * (1 + 2 * Real.pi * n)) * C) hb
  refine ⟨B, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro g
    exact hU g
  · exact ContinuousLinearMap.opNorm_le_bound B (by positivity) hb

/-- The negative-Sobolev error bound for the actual chart-transferred operator
follows from its literal Euclidean adjoint's support and L²-to-H¹ endpoint.
This is the duality deduction in `app:ch_background:prop:bg-frame`, Step 1;
the norm on the right is the existing actual H⁻¹ dual norm. -/
theorem transferOperator_negativeOne_bound {r C : ℝ} (hr : r < 1 / 2) (hC : 0 ≤ C)
    (T : EuclideanL2 n V →L[ℝ] EuclideanL2 n V)
    (hs : ∀ g, ∀ᵐ x ∂volume, x ∉ chartBox r → T.adjoint g x = 0)
    (hT : ∀ g, MemVectorFourierSobolev 1 (l2ComplexInclusion volume (T.adjoint g)) ∧
      vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (T.adjoint g)) ≤ C * ‖g‖)
    (f : PeriodicL2 n V) :
    ‖transferOperator T f‖ ≤ (((m : ℝ) * (1 + 2 * Real.pi * n)) * C) *
      ‖PeriodicSobolevNegativeOne.ofL2 f‖ := by
  obtain ⟨A, hA, hnorm⟩ := exists_transferOperator_adjoint_h1 hr hC T hs hT
  let S := transferOperator T
  have hcompat : PeriodicSobolevSpace.toL2 1 (A (S f)) = S.adjoint (S f) :=
    DFunLike.congr_fun hA (S f)
  have hp := PeriodicSobolevNegativeOne.norm_pairing_le
    (PeriodicSobolevNegativeOne.ofL2 f) (A (S f))
  rw [PeriodicSobolevNegativeOne.pairing_apply, PeriodicSobolevNegativeOne.ofL2_apply,
    hcompat, S.adjoint_inner_right, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hp
  have hb := hp.trans (mul_le_mul_of_nonneg_left
    ((A.le_opNorm (S f)).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))
    (norm_nonneg _))
  by_cases hz : ‖S f‖ = 0
  · change ‖S f‖ ≤ _
    rw [hz]
    positivity
  · have hpos : 0 < ‖S f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖S f‖ ≤ _
    nlinarith [hb]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicEndpoint
