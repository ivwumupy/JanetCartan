module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.ProjectedResidualBound
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.DirectSolverAgreement
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledProduct
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ExtendedPhysicalResidual
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Pointwise stage bounds from the normalized solver's AE residual

The complete normalized physical identity retains its original L² source
class. Its inverse-Gram reconstruction is an almost-everywhere identity.
Apply that identity on the original closed stage core and use the smooth
ambient strain to transfer a quantitative bound to every point, including
the boundary. The fixed frame neighborhood supplies the reconstruction
constant before the varying history.

The sampled consequence concerns exactly the pair field returned by
`exists_normalized_measured_direct_sampled_stage`. It retains the full
source multiplier, both output cutoffs and every doubled plus carrier.
The normalized physical/right-side equations already have actual producers;
complete signed reduced-residual decay still belongs to
`both-response-transfer` and `both-signed-response-estimates`. These deductions
do not assert that decay or complete `UniformHistoryCorrection`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.UniformStep
open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse LocalSobolev
open CorrectedAtoms ProjectedStressFrame CharacteristicTransport.CompleteResidual
open GeometricProfile ResponseTransfer.RetainedFactors RawPrimary ProtectedFlow

/-- The closed physical core in `main:thm:step` is the closure of its open
ball. A continuous strain norm therefore inherits its AE bound at every core
point, without choosing a representative of the underlying residual class. -/
private theorem norm_le_on_core_of_ae {n : ℕ} (D : LocalDomain)
    {E : Type*} [NormedAddCommGroup E] {f : Euclidean n → E} {C : ℝ}
    (hf : ContinuousOn f (D.core n))
    (hbound : ∀ᵐ x ∂volume.restrict (D.core n), ‖f x‖ ≤ C) :
    ∀ x ∈ D.core n, ‖f x‖ ≤ C := by
  have he : (fun x ↦ max ‖f x‖ C) =ᵐ[volume.restrict (D.core n)] (fun _ ↦ C) := by
    filter_upwards [hbound] with x hx
    exact max_eq_right hx
  have hdense : D.core n ⊆ closure (interior (D.core n)) := by
    change closedBall (0 : Euclidean n) D.coreRadius ⊆ _
    rw [← closure_ball (0 : Euclidean n) D.coreRadius_pos.ne']
    exact closure_mono ball_subset_interior_closedBall
  have hpoint := MeasureTheory.Measure.eqOn_of_ae_eq he (fun x hx ↦ (hf.norm x hx).max continuousWithinAt_const)
    continuousOn_const hdense
  intro x hx
  exact (max_le_iff.mp (le_of_eq (hpoint hx))).1

/-- `app:ch_pairs:eq:pairs-lag-sum-error`: transfer the actual normalized
solver's complete AE source discrepancy to a pointwise full-strain bound on
the original closed stage core. Smoothness of the ambient strain and positivity
of Lebesgue measure on open sets justify the boundary-inclusive transfer;
no pointwise interpretation of an arbitrary L² representative is used.
The normalized physical/right-side equations are outputs of
`exists_source_scale_cap_normalized_measured_direct_sampled_size`. The sole
remaining analytic bound is the complete reduced discrepancy, produced by
`both-response-transfer` and `both-signed-response-estimates`. -/
theorem fixedSolver_error_norm_le_of_extended_residual_ae {n : ℕ} (hn : 5 ≤ n)
    (D : LocalDomain) (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean (embeddingDimension n))
    {U S W O core chart Kframe : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (hpU : closedBall p.center p.radius ⊆ U)
    (hSU : S ⊆ U) (hOp : O ⊆ closedBall p.center p.radius)
    (hKframe : IsCompact Kframe) (hKframeU : Kframe ⊆ U)
    (hclose : ∀ i, cNorm Kframe 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
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
    (hDcore : D.core n ⊆ core) (hDO : D.core n ⊆ O) (hDK : D.core n ⊆ Kframe)
    (h : compactSmoothSources S) (hsymm : ∀ x ∈ D.core n, ((h : MetricField n) x).IsSymm)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hresidual :
      let hQ := contDiffOn_projectedStress hU hF hi hrank
      let z := SmallSupport.zeroExtend hW
        (Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU h))
      ∀ᵐ x ∂volume.restrict (D.core n), ∀ a, |A z x a - z x a| ≤ ε) :
    let hQ := contDiffOn_projectedStress hU hF hi hrank
    ∀ x ∈ D.core n, ‖linearizedMetric F
      (fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
        solver hsolver Ξ h) x - (h : MetricField n) x‖ ≤
          projectedStressResidualConstant hn * ε := by
  classical
  let hQ := contDiffOn_projectedStress hU hF hi hrank
  let z := SmallSupport.zeroExtend hW
    (Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU h))
  let ΞD : OutputCutoff (D.core n) chart :=
    { Ξ with plateau := fun x hx ↦ Ξ.plateau (hDcore hx) }
  have hframe (x) (hx : x ∈ D.core n) :=
    projectedStress_tensorFrame_of_cNorm_closeness hn hU hKframe hKframeU
      hF hi hrank hclose (hDK hx)
  have he := fixedSmoothSolverAmbientExtension_extended_error_eq_full_residual_ae
    p F hU hF hi hrank hpU hSU hOp η hη solver right hsolver ΞD hchart hchartU
    Corr A hW hSW hplateau hphysical hright isClosed_closedBall.measurableSet
    hDO h hsymm (fun x hx ↦ (hframe x hx).1)
    (fun x hx ↦ (hframe x hx).2.1) (fun x hx ↦ (hframe x hx).2.2)
  have hsame : fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
      solver hsolver ΞD h = fixedSmoothSolverAmbientExtension F (projectedStress F) η
        hU hQ hη hSU solver hsolver Ξ h := by
    rw [fixedSmoothSolverAmbientExtension_eq_cutoff,
      fixedSmoothSolverAmbientExtension_eq_cutoff]
  dsimp only at he
  rw [hsame] at he
  have hcont := contDiff_fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ
    hη hSU solver hsolver Ξ hchart (hF.mono hchartU)
    (fun x hx ↦ hi x (hchartU hx)) (fun x hx ↦ hrank x (hchartU hx)) h
  apply norm_le_on_core_of_ae D
    (((AmbientResponse.contDiffOn_linearizedMetric hU hF hcont.contDiffOn).sub
      h.property.1.contDiffOn).continuousOn.mono (hDK.trans hKframeU))
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet, he, hresidual] with x hx hex hres
  rw [hex, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hnorm := CurrentMean.norm_inverseGramReconstruction_le (projectedStress F x)
    (fun a ↦ A z x a - z x a)
  rw [inverseGramReconstruction_eq_sum] at hnorm
  calc
    _ ≤ 2 * (∑ i, ∑ a, |(stressGram (projectedStress F x))⁻¹ i a| *
        |A z x a - z x a| * ‖projectedStress F x i‖) :=
      mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ ≤ 2 * (∑ i, ∑ a, |(stressGram (projectedStress F x))⁻¹ i a| *
        ε * ‖projectedStress F x i‖) := by
      gcongr with i a
      exact hres a
    _ = (2 * (∑ i, ∑ a, |(stressGram (projectedStress F x))⁻¹ i a| *
        ‖projectedStress F x i‖)) * ε := by
      simp only [Finset.sum_mul, mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ projectedStressResidualConstant hn * ε :=
      mul_le_mul_of_nonneg_right (projectedStress_residual_coefficient_le hn hU hKframe
        hKframeU hF hi hrank hclose (hDK hx)) hε

/-- `app:ch_pairs:eq:pairs-lag-sum-error` for the literal pair of
`exists_normalized_measured_direct_sampled_stage`. The constructed solver's
complete physical equation is retained, and the individual reduced residual
bounds need only hold almost everywhere on the original closed stage core.
The preceding theorem proves the pointwise transfer, then the existing
sampled-product assembler preserves the original forcing exponent, squared
amplitude and every doubled plus carrier. The original source cutoff is
applied once, and only the difference diagonal is excluded. Complete AE
residual decay remains with `both-response-transfer` and
`both-signed-response-estimates`; no all-word estimate is assumed proved. -/
theorem cut_sampled_fixedSolver_product_stage_error_le_of_ae_residual
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (hn : 5 ≤ n)
    (D : LocalDomain) (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean (embeddingDimension n))
    {U S W O core chart Kframe : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (hpU : closedBall p.center p.radius ⊆ U)
    (hSU : S ⊆ U) (hOp : O ⊆ closedBall p.center p.radius)
    (hKframe : IsCompact Kframe) (hKframeU : Kframe ⊆ U)
    (hclose : ∀ i, cNorm Kframe 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
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
    (hDcore : D.core n ⊆ core) (hDO : D.core n ⊆ O) (hDK : D.core n ⊆ Kframe)
    {Vsource : Set (Euclidean n)} (hVsource : IsOpen Vsource)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχV : tsupport χ ⊆ Vsource) (hχS : tsupport χ ⊆ S)
    (hone : EqOn χ (fun _ ↦ 1) (D.core n))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin (embeddingDimension n)))
    (θ : ι → Euclidean n → ℝ) (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) Vsource)
    {R δ C Ccount Cmass : ℝ} {k q : ℕ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hC : 0 ≤ C) (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hq : 2 * forcingExponent n + 1 + samplingSlack + 2 * (k : ℝ) ≤
      (carrierExponent - separationExponent) * q)
    (hresidual : ∀ (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let tensor := fun x ↦ χ x • (if minus then
        ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x
        else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)
      ∀ hadmit : tensor ∈ compactSmoothSources S,
      let hQ := contDiffOn_projectedStress hU hF hi hrank
      let z := SmallSupport.zeroExtend hW
        (Corr (cutoffStressSmoothSource (W := W) (projectedStress F) η hU hQ hη hSU
          ⟨tensor, hadmit⟩))
      ∀ᵐ x ∂volume.restrict (D.core n), ∀ a,
        |A z x a - z x a| ≤ C * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) :
    let hQ := contDiffOn_projectedStress hU hF hi hrank
    let Bphysical := fixedSmoothSolverAmbientExtension F (projectedStress F) η
      hU hQ hη hSU solver hsolver Ξ
    let Qoff := ProductSum.offSelfSource (δ * R ^ forcingExponent n) μ
      (sampledDerivative Z) (sampledDerivativeAmplitude Z θ)
    ∀ x ∈ D.core n, ‖linearizedMetric F
      (periodicLift (Periodization.cutToTorus (physicalCutoff D)
        (-Bphysical (fun y ↦ χ y • Qoff y)))) x + Qoff x‖ ≤
      (2 * (projectedStressResidualConstant hn * C) * (Ccount * Cmass)) *
        δ * R ^ (-2 * (k : ℝ)) := by
  classical
  let hQ := contDiffOn_projectedStress hU hF hi hrank
  let Bphysical := fixedSmoothSolverAmbientExtension F (projectedStress F) η
    hU hQ hη hSU solver hsolver Ξ
  let Bcut : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean (embeddingDimension n)) := Bphysical.comp (LinearMap.pi fun x ↦ χ x • LinearMap.proj x)
  have hBcut (tensor : MetricField n) :
      Bcut tensor = Bphysical (fun x ↦ χ x • tensor x) := rfl
  have hmem (minus : Bool) (i j : ι) : (fun x ↦ χ x • (if minus then
      ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x
      else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)) ∈
      compactSmoothSources S := by
    have hsmall := sampled_signed_sources_mem Z θ hVsource hZ hχ hχc hχV i j
    cases minus
    · exact ⟨hsmall.1.1, hsmall.1.2.1, hsmall.1.2.2.trans hχS⟩
    · exact ⟨hsmall.2.1, hsmall.2.2.1, hsmall.2.2.2.trans hχS⟩
  have hsmooth (minus : Bool) (i j : ι) : ContDiff ℝ ∞
      (Bcut (if minus then ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j
        else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j)) := by
    have hb := contDiff_fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
      solver hsolver Ξ hchart (hF.mono hchartU)
      (fun x hx ↦ hi x (hchartU hx)) (fun x hx ↦ hrank x (hchartU hx)) ⟨_, hmem minus i j⟩
    cases minus <;> simpa only [Bool.false_eq_true, ite_false, ite_true, hBcut, Bphysical] using hb
  have hresponse (minus : Bool) (i j : ι) (hij : minus = true → i ≠ j)
      (x : Euclidean n) (hx : x ∈ D.core n) :
      ‖linearizedMetric F (Bcut (if minus then
          ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j
          else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j)) x -
        (if minus then ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x
          else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x)‖ ≤
        (projectedStressResidualConstant hn * C) *
          ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ := by
    have hsymm (y : Euclidean n) (_hy : y ∈ D.core n) :
        ((fun y ↦ χ y • (if minus then
          ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j y
          else ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j y)) y).IsSymm := by
      cases minus <;>
        exact (((symmetricBilinearTensor_isSymm _ _).smul _).map Complex.re).smul _
    have hb := fixedSolver_error_norm_le_of_extended_residual_ae hn D p F hU hF hi hrank
      hpU hSU hOp hKframe hKframeU hclose η hη solver right hsolver Ξ hchart hchartU
      Corr A hW hSW hplateau hphysical hright hDcore hDO hDK ⟨_, hmem minus i j⟩
      hsymm (by positivity) (hresidual minus i j hij (hmem minus i j)) x hx
    cases minus <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
      hone hx, one_smul, mul_assoc, hBcut, Bphysical] using hb
  exact cut_sampled_product_stage_error_le D F Bcut μ hμ Z θ
    (sampledDerivativeAmplitude Z θ) (sampledDerivative_eq_phase_smul_amplitude Z θ)
    (hsmooth false) (fun i j _ ↦ hsmooth true i j)
    hR hδ hδone (mul_nonneg (projectedStressResidualConstant_pos hn).le hC)
    hCcount hCmass hcount hmass hq
    (fun i j x hx ↦ hresponse false i j (by simp) x hx)
    (fun i j hij x hx ↦ hresponse true i j (fun _ ↦ Ne.symm hij) x hx)

end JanetCartan.UniformStep
