module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverResidual
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedSourceAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles

/-!
# The normalized extended equation on the original geometric core

The normalized inverse uses the full extended coefficient array. On the
original coefficient ball its physical action is exactly the geometric one,
including the connection matrix. This transfers its complete source residual
to the same ambient completion without identifying independently chosen maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open CharacteristicTransport.CompleteResidual GeometricProfile ProtectedFlow
open ProjectedStressFrame ResponseTransfer.RetainedFactors PrimarySourceAdmission
open FixedDomainInverse LocalSobolev ResponseSourceExtension
open NullTransport

/-- The full extended physical action agrees with the actual geometric action
on the unchanged coefficient ball. The zeroth-order matrix retains every
Christoffel entry (`app:ch_regular:eq:coefficient-extension`,
`app:ch_waves:eq:reduced-symbol`). -/
theorem physicalWeakApply_extendedProjectedStress_eq
    {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) {y : Euclidean n}
    (hy : y ∈ closedBall p.center p.radius) (hF : ContDiffAt ℝ 2 F y)
    (hrank : Set.range (normalMap F y) = (normalSpace F y : Set (Euclidean N)))
    (v : Euclidean n → Fin n → ℂ)
    (D : Euclidean n → Euclidean n →L[ℝ] (Fin n → ℂ)) :
    physicalWeakApply
      (fun x a ↦ ActualCarriers.pencil (extendedProjectedStress p F x)
        (EuclideanSpace.single a 1))
      (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      v D y =
    physicalWeakApply
      (fun x a ↦ ActualCarriers.pencil (projectedStress F x) (EuclideanSpace.single a 1))
      (fun x ↦ reducedZerothCoefficient F (projectedStress F x) x) v D y := by
  have hQ := affineFrameExtension_eqOn p (projectedStress F) hy
  have hB := reducedZerothProjection_extended_eqOn p F hy
  have hgeo : (fun i ↦ (StressFrame.geometricCubeStress F y i).val) =
      projectedStress F y :=
    funext (ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress hF hrank)
  dsimp only at hB
  rw [hgeo] at hB
  change extendedProjectedStress p F y = projectedStress F y at hQ
  ext i
  simp only [physicalWeakApply, hQ, hB]

/-- The normalized solver's extended physical equation gives the original
ambient inverse-Gram residual on the SAME core and corrected source. The
source operator and correction are retained literally; only coefficient
agreement on the original ball is used
(`app:ch_response:eq:response-full-identity`, `app:ch_regular:eq:exact-physical`). -/
theorem fixedSmoothSolverAmbientExtension_extended_error_eq_full_residual_ae
    {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) {U S W O core chart : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (hpU : closedBall p.center p.radius ⊆ U)
    (hSU : S ⊆ U) (hOp : O ⊆ closedBall p.center p.radius)
    (η : Euclidean n → ℝ) (hη : ContDiff ℝ ∞ η)
    (solver right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
    (hW : MeasurableSet W) (hSW : S ⊆ W) (hplateau : S ⊆ {x | η x = 1})
    (hphysical : ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (extendedProjectedStress p F y)
        (EuclideanSpace.single a 1))
      (reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O)
    (hright : ∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
      (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
        A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v)))
    (hcore : MeasurableSet core) (hcoreO : core ⊆ O)
    (h : compactSmoothSources S) (hsymm : ∀ x ∈ core, ((h : MetricField n) x).IsSymm)
    (hQsymm : ∀ x ∈ core, ∀ i, (projectedStress F x i).IsSymm)
    (hQlin : ∀ x ∈ core, LinearIndependent ℝ (projectedStress F x))
    (hspan : ∀ x ∈ core,
      (Submodule.span ℝ (range (projectedStress F x)) : Set (MetricTensor n)) = stressSpace F x) :
    let hQ := contDiffOn_projectedStress hU hF hi hrank
    (fun x ↦ linearizedMetric F
      (fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
        solver hsolver Ξ h) x - (h : MetricField n) x) =ᵐ[volume.restrict core]
      (fun x ↦ (2 : ℝ) • ∑ i, ∑ j, ((stressGram (projectedStress F x))⁻¹ i j *
        (A (SmallSupport.zeroExtend hW
          (Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU h))) x j -
          SmallSupport.zeroExtend hW
            (Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU h)) x j)) •
              projectedStress F x i) := by
  apply fixedSmoothSolverAmbientExtension_error_eq_full_residual_ae
    F (projectedStress F) η hU (contDiffOn_projectedStress hU hF hi hrank) hη hSU
    solver right hsolver Ξ hchart (hF.mono hchartU)
    (fun x hx ↦ hi x (hchartU hx)) (fun x hx ↦ hrank x (hchartU hx))
    Corr A hW hSW hplateau _ hright hcore hcoreO h hsymm hQsymm hQlin hspan
  intro v x hx
  have he := hphysical v hx
  rw [physicalWeakApply_extendedProjectedStress_eq p F (hOp hx)
    ((hF.contDiffAt (hU.mem_nhds (hpU (hOp hx)))).of_le (by simp))
    (hrank x (hpU (hOp hx)))] at he
  exact he

end JanetCartan.CorrectedAtoms
