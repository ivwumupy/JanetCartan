module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.DirectResidualTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledEstimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.QuadratureResidual
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Hermitian
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Primary strain from the same normalized source residual

The primary in `main:eq:primary-strain` uses the real quadrature of the final
complex atom.  The normalized solver gives an almost-everywhere equation for
each original source quadrature.  Apply the fixed-frame reconstruction bound
to both, then transfer the result to the literal corrected atom and its finite
canonical sum.  The original source and output cutoffs stay fixed.

The remaining quantitative premise is decay of the complete corrected-source
discrepancy, whose producer is the same-inverse mixed-word localization proof.
The exact physical equation, source admission, and canonical input budgets have
separate existing producers; these deductions do not assert their instantiation.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.UniformStep

open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse LocalSobolev
open CorrectedAtoms ProjectedStressFrame CharacteristicTransport.CompleteResidual
open GeometricProfile ResponseTransfer.RetainedFactors RawPrimary ProtectedFlow

/-- Realification contracts the complete strain of the actual complex primary
(`main:eq:primary-strain`).  Differentiability is checked before commuting the
real-part map with the physical derivative. -/
theorem linearizedMetric_realPart_eq {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {Z : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hZ : DifferentiableAt ℝ Z x) :
    linearizedMetric F (euclideanRealPart ∘ Z) x =
      (WKB.complexLinearizedMetric F Z x).map Complex.re := by
  have hd : fderiv ℝ (euclideanRealPart ∘ Z) x =
      euclideanRealPart.comp (fderiv ℝ Z x) :=
    (euclideanRealPart.hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  ext a b
  simp only [linearizedMetric, partialDeriv, hd]
  simp [WKB.complexLinearizedMetric, partialDeriv, PiLp.inner_apply,
    RCLike.inner_apply, Finset.sum_add_distrib, mul_comm]

/-- The same real quadrature used in `sampledPrimary` has no larger Frobenius
strain norm than its complex atom (`main:eq:primary-strain`). -/
theorem norm_linearizedMetric_realPart_le {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {Z : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hZ : DifferentiableAt ℝ Z x) :
    ‖linearizedMetric F (euclideanRealPart ∘ Z) x‖ ≤
      ‖WKB.complexLinearizedMetric F Z x‖ := by
  rw [linearizedMetric_realPart_eq F hZ]
  exact frobenius_norm_re_le _

/-- `app:ch_response:cor:current-atoms` and `main:eq:primary-strain`: apply the
same normalized solver's complete AE source discrepancy to both quadratures
of a literal corrected primary.  The fixed reconstruction constant is chosen
before the source and its accuracy.  The boundary-inclusive transfer is the
proved real transfer, applied to the two admitted complete cutoff sources.

For canonical raw data, `fullPrimaryWave_source_quadratures_mem` supplies the
two source admissions.  The normalized solver supplies `hphysical` and
`hright`; the all-word observation proof supplies `hresidualR` and `hresidualI`.
-/
theorem complexCorrectedAtom_strain_le_of_extended_residual_ae {n : ℕ} (hn : 5 ≤ n)
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
    (χ : Euclidean n → ℝ) (hχcore : ∀ x ∈ D.core n, χ x = 1)
    (Zraw : Euclidean n → EuclideanSpace ℂ (Fin (embeddingDimension n)))
    {X : Set (Euclidean n)} (hX : IsOpen X) (hDX : D.core n ⊆ X)
    (hraw : ContDiffOn ℝ ∞ Zraw X)
    (hR : tensorFieldRealPart (complexAtomicSource F χ Zraw) ∈ compactSmoothSources S)
    (hI : tensorFieldImagPart (complexAtomicSource F χ Zraw) ∈ compactSmoothSources S)
    {εR εI : ℝ} (hεR : 0 ≤ εR) (hεI : 0 ≤ εI)
    (hresidualR :
      let hQ := contDiffOn_projectedStress hU hF hi hrank
      let z := SmallSupport.zeroExtend hW (Corr (cutoffStressSmoothSource (W := W)
        (projectedStress F) η hU hQ hη hSU ⟨_, hR⟩))
      ∀ᵐ x ∂volume.restrict (D.core n), ∀ a, |A z x a - z x a| ≤ εR)
    (hresidualI :
      let hQ := contDiffOn_projectedStress hU hF hi hrank
      let z := SmallSupport.zeroExtend hW (Corr (cutoffStressSmoothSource (W := W)
        (projectedStress F) η hU hQ hη hSU ⟨_, hI⟩))
      ∀ᵐ x ∂volume.restrict (D.core n), ∀ a, |A z x a - z x a| ≤ εI) :
    let hQ := contDiffOn_projectedStress hU hF hi hrank
    let B := fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
      solver hsolver Ξ
    ∀ x ∈ D.core n,
      ‖WKB.complexLinearizedMetric F (complexCorrectedAtom F χ B Zraw) x‖ ≤
        projectedStressResidualConstant hn * (εR + εI) := by
  intro hQ B
  let H := complexAtomicSource F χ Zraw
  have hreg (h : compactSmoothSources S) : ContDiff ℝ ∞ (B h) :=
    contDiff_fixedSmoothSolverAmbientExtension F (projectedStress F) η hU hQ hη hSU
      solver hsolver Ξ hchart (hF.mono hchartU)
      (fun x hx ↦ hi x (hchartU hx)) (fun x hx ↦ hrank x (hchartU hx)) h
  have hBR := hreg ⟨_, hR⟩
  have hBI := hreg ⟨_, hI⟩
  have hB := contDiff_complexifyResponse B H hBR hBI
  have heR := fixedSolver_error_norm_le_of_extended_residual_ae hn D p F hU hF hi hrank
    hpU hSU hOp hKframe hKframeU hclose η hη solver right hsolver Ξ hchart hchartU
    Corr A hW hSW hplateau hphysical hright hDcore hDO hDK ⟨_, hR⟩
    (fun x _ ↦ (complexAtomicSource_isSymm F χ Zraw x).map Complex.re) hεR hresidualR
  have heI := fixedSolver_error_norm_le_of_extended_residual_ae hn D p F hU hF hi hrank
    hpU hSU hOp hKframe hKframeU hclose η hη solver right hsolver Ξ hchart hchartU
    Corr A hW hSW hplateau hphysical hright hDcore hDO hDK ⟨_, hI⟩
    (fun x _ ↦ (complexAtomicSource_isSymm F χ Zraw x).map Complex.im) hεI hresidualI
  intro x hx
  have hrawAt := (hraw.contDiffAt (hX.mem_nhds (hDX hx))).differentiableAt (by simp)
  rw [complexCorrectedAtom_strain F χ B Zraw (hχcore x hx) hrawAt
      (hB.differentiable (by simp) x), norm_neg,
    complexAtomicResidual_eq_quadratures F B H (hBR.differentiable (by simp) x)
      (hBI.differentiable (by simp) x)]
  calc
    _ ≤ ‖(linearizedMetric F (B (tensorFieldRealPart H)) x - tensorFieldRealPart H x).map
          Complex.ofReal‖ +
        ‖Complex.I • (linearizedMetric F (B (tensorFieldImagPart H)) x -
          tensorFieldImagPart H x).map Complex.ofReal‖ := norm_add_le _ _
    _ = ‖linearizedMetric F (B (tensorFieldRealPart H)) x - tensorFieldRealPart H x‖ +
        ‖linearizedMetric F (B (tensorFieldImagPart H)) x - tensorFieldImagPart H x‖ := by
      rw [norm_smul, Complex.norm_I, one_mul,
        Matrix.frobenius_norm_map_eq _ Complex.ofReal Complex.norm_real,
        Matrix.frobenius_norm_map_eq _ Complex.ofReal Complex.norm_real]
    _ ≤ projectedStressResidualConstant hn * εR +
        projectedStressResidualConstant hn * εI := add_le_add (heR x hx) (heI x hx)
    _ = _ := by ring

end JanetCartan.UniformStep
