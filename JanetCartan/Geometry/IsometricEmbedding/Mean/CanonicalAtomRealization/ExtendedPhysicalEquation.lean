module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedSourceAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverResidual
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles

/-!
# The normalized physical equation on the admitted coefficient ball

The normalized inverse solves with the original affine extension of the full
reduced coefficient array. On the admitted ball this array is the physical
history's projected stress and its full Christoffel contraction. Identify the
literal physical action there, then transfer the SAME smooth solution and right
side to the geometric equation consumed by
`CorrectedAtoms.fixedSmoothSolverAmbientExtension_error_eq_inverseGram`.

No source error is removed, and no new solver or frame is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open ProtectedFlow ProjectedStressFrame ResponseTransfer.RetainedFactors
open GeometricProfile
open CorrectedAtoms NullTransport CharacteristicTransport.CompleteResidual

/-- On the original coefficient ball, the extended physical action is the
actual covariant reduced operator, including every lower-order connection term
(`app:ch_regular:eq:coefficient-extension`, `app:ch_waves:eq:reduced-symbol`). -/
theorem physicalWeakApply_extendedProjectedStress_eq_reducedOperator {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) {x : Euclidean n}
    (hx : x ∈ closedBall p.center p.radius) (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    {u : Euclidean n → Euclidean n} (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (extendedProjectedStress p F y)
        (EuclideanSpace.single a 1))
      (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      (fun y ↦ (euclideanComplexInclusion (u y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (u y)).ofLp)) x i =
      (reducedOperator F (projectedStress F) u x i : ℂ) := by
  have hQ : extendedProjectedStress p F x = projectedStress F x :=
    affineFrameExtension_eqOn p (projectedStress F) hx
  have hB : (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F) x =
      reducedZerothCoefficient F (projectedStress F x) x := by
    exact (reducedZerothProjection_extended_eqOn p F hx).trans
      (congrArg (fun A ↦ reducedZerothCoefficient F A x)
        (funext (fun j ↦
          ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress hF hrank j)))
  have he := physicalWeakApply_geometric_eq F (projectedStress F)
    (fun j ↦ (projectedStress_mem_stressSpace hF hrank j).1) hu i
  simpa only [physicalWeakApply, hQ, hB] using he

/-- The SAME normalized solver and complete right side satisfy the original
geometric equation on an admitted core. This discharges the coefficient-identity
input of `fixedSmoothSolverAmbientExtension_error_eq_inverseGram`; the complete
source discrepancy remains in `right`
(`app:ch_regular:eq:exact-physical`, `app:ch_response:eq:response-full-identity`). -/
theorem physicalEquation_projectedStress_of_extended
    {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) {U O W : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    (hOU : O ⊆ U) (hOp : O ⊆ closedBall p.center p.radius)
    (solver right : FixedDomainInverse.smoothSource W (Euclidean n) →ₗ[ℝ]
      (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hphysical : ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (extendedProjectedStress p F y)
        (EuclideanSpace.single a 1))
      (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O) :
    ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (projectedStress F y) (EuclideanSpace.single a 1))
      (fun y ↦ reducedZerothCoefficient F (projectedStress F y) y)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O := by
  intro v x hx
  have hFx : ContDiffAt ℝ 2 F x :=
    (hF.contDiffAt (hU.mem_nhds (hOU hx))).of_le (by simp)
  have hrankx := hrank x (hOU hx)
  have hv := (hsolver v).differentiable (by simp) x
  funext i
  have he := congrFun (hphysical v hx) i
  rw [physicalWeakApply_extendedProjectedStress_eq_reducedOperator p F (hOp hx) hFx hrankx hv i] at he
  rw [physicalWeakApply_geometric_eq F (projectedStress F)
    (fun j ↦ (projectedStress_mem_stressSpace hFx hrankx j).1) hv i]
  exact he

end JanetCartan.CanonicalAtomRealization
