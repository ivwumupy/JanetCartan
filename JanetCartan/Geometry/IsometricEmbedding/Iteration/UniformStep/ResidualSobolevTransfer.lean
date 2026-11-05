module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.DirectResidualTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ResidualSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedQuadratures

/-!
# From the normalized source Sobolev estimate to the actual stage strain

The finite angular observation and the mixed residual words are estimated in
restriction Sobolev norms. The stage consumes coordinate bounds almost
everywhere on its closed core. The normalized solver's smooth right-hand side
identifies these two quantities on the same corrected source. Local Sobolev
embedding supplies one constant before the fields, histories and samples.

This transfer keeps the original source multiplier, restriction measure and
zero extension. Sobolev membership is proved from the actual smooth right-hand
side. Quantitative decay of the complete corrected source remains the output
required from the mixed-word and finite-remainder producers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.UniformStep
open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse LocalSobolev
open CorrectedAtoms AmbientResponse ProjectedStressFrame CharacteristicTransport.CompleteResidual
open GeometricProfile ResponseTransfer.RetainedFactors RawPrimary ProtectedFlow

/-- `app:ch_pairs:eq:pairs-lag-sum-error`: the local Sobolev embedding constant
for the complete normalized source discrepancy, fixed before all histories,
sources and sample choices. -/
def residualSobolevEmbeddingConstant (n : ℕ) : ℝ :=
  (exists_smoothRight_fullResidual_cNorm_bound n 0).choose

/-- `app:ch_pairs:eq:pairs-lag-sum-error`: positivity of the fixed embedding
constant used by the sampled stage transfer. -/
theorem one_le_residualSobolevEmbeddingConstant (n : ℕ) :
    1 ≤ residualSobolevEmbeddingConstant n :=
  (exists_smoothRight_fullResidual_cNorm_bound n 0).choose_spec.1

/-- The actual smooth right-hand side proves Sobolev membership of the SAME
complete corrected-source discrepancy and controls its coordinates almost
everywhere on the original closed core (`app:ch_regular:eq:exact-physical`,
`app:ch_pairs:eq:pairs-lag-sum-error`). The residual class is never identified
pointwise with an arbitrary representative. The smooth-right identity is an
output of `exists_source_scale_cap_normalized_measured_direct_sampled_size`;
the exact norm on the right is consumed from the finite-observation and
mixed-word estimates. -/
theorem fullResidual_ae_coordinate_le_restrictionSobolevNorm {n : ℕ}
    (D : LocalDomain) (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W O : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ a, ContDiffOn ℝ ∞ (fun x ↦ Q x a) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsmooth : ∀ v, ContDiff ℝ ∞ (right v))
    (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
    (hW : MeasurableSet W) (hSW : S ⊆ W) (hplateau : S ⊆ {x | η x = 1})
    (hright : ∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
      (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
        A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v)))
    {Rout : ℝ} (hcoreR : D.coreRadius < Rout) (hRO : ball (0 : Euclidean n) Rout ⊆ O)
    (h : compactSmoothSources S) :
    let z := SmallSupport.zeroExtend hW
      (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))
    let e := A z - z
    let eV := ((Lp.memLp e).restrict (ball (0 : Euclidean n) Rout)).toLp e
    (∀ m, MemRestrictionSobolev (ball (0 : Euclidean n) Rout) m eV) ∧
    ∀ᵐ x ∂volume.restrict (D.core n), ∀ a,
      |A z x a - z x a| ≤ residualSobolevEmbeddingConstant n *
        restrictionSobolevNorm (ball (0 : Euclidean n) Rout) (n+1) eV := by
  intro z e eV
  let v := cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h
  let f := fun x ↦ right v x - WithLp.toLp 2 (stressSource Q h x)
  have hbound := (exists_smoothRight_fullResidual_cNorm_bound n 0).choose_spec.2
    Q η S U W O hU hQ hη hSU right hsmooth Corr A hW hSW hplateau hright
    0 D.coreRadius Rout D.coreRadius_pos hcoreR hRO h
  have hcut : euclideanCutoffStressSource Q η h =
      fun x ↦ WithLp.toLp 2 (stressSource Q h x) := by
    funext x
    change WithLp.toLp 2 (cutoffSource η (stressSource Q h) x) = _
    rw [cutoffSource_stressSource_eq Q η h
      (fun y hy ↦ hplateau (h.property.2.2 (subset_tsupport _ hy)))]
  have hf : ContDiff ℝ ∞ f := by
    have hf' := (hsmooth v).sub (contDiff_euclideanCutoffStressSource Q η hU hQ hη hSU h)
    simpa only [hcut] using hf'
  have he : f =ᵐ[volume.restrict (D.core n)] (fun x ↦ A z x - z x) :=
    ae_restrict_of_ae_restrict_of_subset ((closedBall_subset_ball hcoreR).trans hRO)
      (smoothRight_cutoffStress_residual_ae Q η hU hQ hη hSU
        right Corr A hW hSW hplateau hright h)
  refine ⟨hbound.1, ?_⟩
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet, he] with x hx hex
  intro a
  have hcoord : |(f x) a| ≤ ‖f x‖ := PiLp.norm_apply_le (f x) a
  have hpoint : ‖f x‖ ≤ cNorm (D.core n) 0 f :=
    norm_le_cNorm (isCompact_closedBall _ _) (hf.of_le (by simp)) hx
  have hestimate : cNorm (D.core n) 0 f ≤ residualSobolevEmbeddingConstant n *
      restrictionSobolevNorm (ball (0 : Euclidean n) Rout) (n+1) eV := by
    simpa only [Nat.zero_add, residualSobolevEmbeddingConstant, LocalDomain.core,
      f, v, eV, e, z] using hbound.2
  have hfinal := hcoord.trans (hpoint.trans hestimate)
  simpa only [hex, PiLp.sub_apply] using hfinal

open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ArbitraryAccuracy.ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The norm used by the stage transfer is literally the normalized angular
observation on the SAME local datum (`app:ch_regular:eq:finite-observation`,
`app:ch_pairs:eq:pairs-lag-one-error`). This equality preserves the original
restriction and zero extension and subtracts exactly one identity. Applying
it to `Corr v` connects the finite-word estimates to the physical strain
without identifying an L² representative pointwise. -/
theorem normalizedSourceDiscrepancy_restriction_eq
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : Euclidean (d+1) → ℝ) (ho : Continuous output)
    (hob : ∀ y, ‖output y‖ ≤ 1) {W : Set (Euclidean (d+1))}
    (hW : MeasurableSet W) (V : Set (Euclidean (d+1))) (v : LocalL2 W (Euclidean (d+1))) :
    let z := SmallSupport.zeroExtend hW v
    let e := realSource f hK L₀ output ho hob z - z
    ((Lp.memLp e).restrict V).toLp e =
      localRealCompression hW V (pairedSource f hK L₀ output ho hob - 1) v := by
  intro z e
  apply Lp.ext
  have hlocal := localRealCompression_coeFn hW V
    (pairedSource f hK L₀ output ho hob - 1) v
  rw [← SignedProductEstimates.normalizedSource_real_defect_eq_compression] at hlocal
  exact (MemLp.coeFn_toLp _).trans hlocal.symm

/-- Apply the normalized angular Sobolev observation to the literal sampled
pair field, using the SAME smooth right-hand side and corrected L² source
(`app:ch_pairs:eq:pairs-lag-sum-error`, `main:eq:metric-ledger`). The preceding
transfer proves the AE coordinate bound and all required Sobolev membership;
the existing stage synthesis supplies the closed-core pointwise strain bound.
The embedding constant depends only on dimension and precedes all histories
and samples. The original forcing exponent, squared amplitude, doubled plus
carriers and exclusion only of the difference diagonal are unchanged.

The sole decay input is the displayed restriction norm of the complete
normalized angular observation. Its producer is the same-inverse finite
angular observation plus every mixed residual word. The smooth-right and
physical equations are outputs of the actual measured direct construction.
This theorem does not assert decay or completion of `UniformHistoryCorrection`.
-/
theorem cut_sampled_fixedSolver_product_stage_error_le_of_normalized_sobolev
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 5 ≤ (d+1))
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : Euclidean (d+1) → ℝ) (ho : Continuous output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (D : LocalDomain) (p : BallExtension.Parameters (Euclidean (d+1)))
    (F : Euclidean (d+1) → Euclidean (embeddingDimension (d+1)))
    {U S W O core chart Kframe : Set (Euclidean (d+1))}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (hpU : closedBall p.center p.radius ⊆ U)
    (hSU : S ⊆ U) (hOp : O ⊆ closedBall p.center p.radius)
    (hKframe : IsCompact Kframe) (hKframeU : Kframe ⊆ U)
    (hclose : ∀ i, cNorm Kframe 6 (fun x ↦ projectedStress F x i - cubeStress (d+1) i) <
      ambientStrainFrameThreshold hn)
    (η : Euclidean (d+1) → ℝ) (hη : ContDiff ℝ ∞ η)
    (solver right : smoothSource W (Euclidean (d+1)) →ₗ[ℝ] (Euclidean (d+1) → Euclidean (d+1)))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hrightSmooth : ∀ v, ContDiff ℝ ∞ (right v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (Corr : LocalL2 W (Euclidean (d+1)) →L[ℝ] LocalL2 W (Euclidean (d+1)))
    (hW : MeasurableSet W) (hSW : S ⊆ W) (hplateau : S ⊆ {x | η x = 1})
    (hphysical : ∀ v, EqOn (physicalWeakApply
      (fun y a ↦ ActualCarriers.pencil (extendedProjectedStress p F y)
        (EuclideanSpace.single a 1))
      (reducedZerothProjection (d+1) ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F)
      (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
      (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O)
    (hright : ∀ v : smoothSource W (Euclidean (d+1)), right v =ᵐ[volume.restrict O]
      (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean (d+1))) +
        realSource f hK L₀ output ho hob (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v)))
    (hDcore : D.core (d+1) ⊆ core) (hDK : D.core (d+1) ⊆ Kframe)
    {Rout : ℝ} (hcoreR : D.coreRadius < Rout) (hRO : ball (0 : Euclidean (d+1)) Rout ⊆ O)
    {Vsource : Set (Euclidean (d+1))} (hVsource : IsOpen Vsource)
    (χ : Euclidean (d+1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχV : tsupport χ ⊆ Vsource) (hχS : tsupport χ ⊆ S)
    (hone : EqOn χ (fun _ ↦ 1) (D.core (d+1)))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean (d+1) → EuclideanSpace ℂ (Fin (embeddingDimension (d+1))))
    (θ : ι → Euclidean (d+1) → ℝ) (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) Vsource)
    {R δ C Ccount Cmass : ℝ} {k q : ℕ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hC : 0 ≤ C) (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hq : 2 * forcingExponent (d+1) + 1 + samplingSlack + 2 * (k : ℝ) ≤
      (carrierExponent - separationExponent) * q)
    (hresidual : ∀ (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let tensor := fun x ↦ χ x • (if minus then
        ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x
        else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)
      ∀ hadmit : tensor ∈ compactSmoothSources S,
      let hQ := contDiffOn_projectedStress hU hF hi hrank
      let v := Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU
        ⟨tensor, hadmit⟩)
      restrictionSobolevNorm (ball (0 : Euclidean (d+1)) Rout) (d+2)
        (localRealCompression hW (ball (0 : Euclidean (d+1)) Rout)
          (pairedSource f hK L₀ output ho hob - 1) v) ≤
        C * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) :
    let hQ := contDiffOn_projectedStress hU hF hi hrank
    let Bphysical := fixedSmoothSolverAmbientExtension F (projectedStress F) η
      hU hQ hη hSU solver hsolver Ξ
    let Qoff := ProductSum.offSelfSource (δ * R ^ forcingExponent (d+1)) μ
      (sampledDerivative Z) (sampledDerivativeAmplitude Z θ)
    ∀ x ∈ D.core (d+1), ‖linearizedMetric F
      (periodicLift (Periodization.cutToTorus (physicalCutoff D)
        (-Bphysical (fun y ↦ χ y • Qoff y)))) x + Qoff x‖ ≤
      (2 * (projectedStressResidualConstant hn *
        (residualSobolevEmbeddingConstant (d+1) * C)) * (Ccount * Cmass)) *
        δ * R ^ (-2 * (k : ℝ)) := by
  intro hQ Bphysical Qoff
  have hEmb : 0 ≤ residualSobolevEmbeddingConstant (d+1) :=
    zero_le_one.trans (one_le_residualSobolevEmbeddingConstant (d+1))
  have hDO : D.core (d+1) ⊆ O := (closedBall_subset_ball hcoreR).trans hRO
  apply cut_sampled_fixedSolver_product_stage_error_le_of_ae_residual hn D p F
    hU hF hi hrank hpU hSU hOp hKframe hKframeU hclose η hη solver right hsolver Ξ
    hchart hchartU Corr (realSource f hK L₀ output ho hob) hW hSW hplateau
    hphysical hright hDcore hDO hDK
    hVsource χ hχ hχc hχV hχS hone μ hμ Z θ hZ hR hδ hδone
    (mul_nonneg hEmb hC) hCcount hCmass hcount hmass hq
  intro minus i j hdiag tensor hadmit hQ' z
  have hcoordinates := (fullResidual_ae_coordinate_le_restrictionSobolevNorm
    D (projectedStress F) η hU hQ' hη hSU right hrightSmooth Corr
    (realSource f hK L₀ output ho hob) hW hSW hplateau hright hcoreR hRO ⟨tensor, hadmit⟩).2
  have hnorm := hresidual minus i j hdiag hadmit
  dsimp only at hnorm
  rw [← normalizedSourceDiscrepancy_restriction_eq f hK L₀ output ho hob] at hnorm
  filter_upwards [hcoordinates] with x hx
  intro a
  exact (hx a).trans ((mul_le_mul_of_nonneg_left hnorm hEmb).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.UniformStep
