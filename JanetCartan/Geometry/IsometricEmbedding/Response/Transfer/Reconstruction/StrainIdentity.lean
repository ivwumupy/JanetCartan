module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Complex
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Strain

/-!
# Exact complex full-tensor response identity

The complex extension of `app:ch_response:eq:response-full-identity` for the
actual coefficient reconstruction. The physical reduced equation is supplied
on both real quadratures. Smoothness, immersion and full normal rank give the
regularity needed to differentiate the published quadrature identities.

The consumer is the full strain estimate in `app:ch_response:prop:response-graded`.
Polynomial multiplier costs and the choice of residual precision are separate
quantitative obligations; this module proves the exact tensor identity only.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer

/-- Coordinate projection used to pass smoothness to each real quadrature in
`app:ch_response:prop:response-ambient`. -/
private def vectorQuadrature {n : ℕ} (q : ℂ →L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin n) →L[ℝ] Euclidean n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ WithLp.toLp 2 (fun i ↦ q (v i))
      map_add' := by intros; ext; simp
      map_smul' := by intro a v; ext i; exact q.map_smul a (v i) }

/-- Real quadratures with the existing Frobenius tensor norm, for
`app:ch_response:eq:response-full-identity`. -/
private def tensorQuadrature {n : ℕ} (q : ℂ →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h i j ↦ q (h i j)
      map_add' := by intros; ext; simp
      map_smul' := by intro a v; ext i j; exact q.map_smul a (v i j) }

/-- Differentiating a local quadrature decomposition identifies the shared
complex metric with the two real metrics (`app:ch_response:prop:response-ambient`). -/
private theorem complexLinearizedMetric_of_eventuallyEq_quadratures {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {W : Euclidean n → EuclideanSpace ℂ (Fin N)}
    {R I : Euclidean n → Euclidean N} {x : Euclidean n}
    (hR : DifferentiableAt ℝ R x) (hI : DifferentiableAt ℝ I x)
    (hW : W =ᶠ[𝓝 x] fun y ↦ euclideanComplexInclusion (R y) +
      Complex.I • euclideanComplexInclusion (I y)) (i j : Fin n) :
    (WKB.complexLinearizedMetric F W x i j).re = linearizedMetric F R x i j ∧
    (WKB.complexLinearizedMetric F W x i j).im = linearizedMetric F I x i j := by
  have hd := ((euclideanComplexInclusion.hasFDerivAt.comp x hR.hasFDerivAt).add
    ((euclideanComplexInclusion.hasFDerivAt.comp x hI.hasFDerivAt).const_smul
      Complex.I)).congr_of_eventuallyEq hW
  have hp (a : Fin n) : partialDeriv W x a =
      euclideanComplexInclusion (partialDeriv R x a) +
      Complex.I • euclideanComplexInclusion (partialDeriv I x a) := by
    exact congrArg (fun L : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N) ↦
      L (EuclideanSpace.single a 1)) hd.fderiv
  simp [WKB.complexLinearizedMetric, hp, linearizedMetric, PiLp.inner_apply,
    RCLike.inner_apply, Finset.sum_add_distrib, mul_comm]

/-- Exact complex full tensor identity from `app:ch_response:eq:response-full-identity`.
The two physical equations are the real quadratures of
`app:ch_regular:eq:exact-physical`, retaining the entire signed residual.
The conclusion uses the shared Frobenius inverse-Gram reconstruction. -/
theorem completedVariationComplex_error_eq_full_residual {n N m : ℕ}
    {F : Euclidean n → Euclidean N}
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)}
    {h : Euclidean n → Matrix (Fin n) (Fin n) ℂ}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s)
    (hhSmooth : ContDiffOn ℝ ∞ h s)
    {x : Euclidean n} (hx : x ∈ s) (hh : (h x).IsSymm)
    {Q : Fin m → MetricTensor n} (hQ : LinearIndependent ℝ Q)
    (hspan : (Submodule.span ℝ (Set.range Q) : Set (MetricTensor n)) = stressSpace F x)
    (z : Euclidean n → Fin m → ℂ)
    (A : (Euclidean n → Fin m → ℂ) →ₗ[ℂ] (Euclidean n → Fin m → ℂ))
    (hphysicalRe : ∀ j, tensorPairing (Q j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).re)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q j) (fun i k ↦ (h x i k).re) +
        (A z x j - z x j).re)
    (hphysicalIm : ∀ j, tensorPairing (Q j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).im)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q j) (fun i k ↦ (h x i k).im) +
        (A z x j - z x j).im) :
    WKB.complexLinearizedMetric F (completedVariationComplex F u h) x - h x =
      (2 : ℂ) • WKB.stressReconstruction Q (fun j ↦ A z x j - z x j) := by
  let uR : Euclidean n → Euclidean n := fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).re)
  let uI : Euclidean n → Euclidean n := fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).im)
  let hR : MetricField n := fun y i j ↦ (h y i j).re
  let hI : MetricField n := fun y i j ↦ (h y i j).im
  have huR : ContDiffOn ℝ ∞ uR s :=
    (vectorQuadrature Complex.reCLM).contDiff.comp_contDiffOn hu
  have huI : ContDiffOn ℝ ∞ uI s :=
    (vectorQuadrature Complex.imCLM).contDiff.comp_contDiffOn hu
  have hhR : ContDiffOn ℝ ∞ hR s :=
    (tensorQuadrature Complex.reCLM).contDiff.comp_contDiffOn hhSmooth
  have hhI : ContDiffOn ℝ ∞ hI s :=
    (tensorQuadrature Complex.imCLM).contDiff.comp_contDiffOn hhSmooth
  have hWR := AmbientResponse.contDiffOn_completedVariation hs hF huR hhR himm hrank
  have hWI := AmbientResponse.contDiffOn_completedVariation hs hF huI hhI himm hrank
  have hW : completedVariationComplex F u h =ᶠ[𝓝 x] fun y ↦
      euclideanComplexInclusion (AmbientResponse.completedVariation F uR hR y) +
        Complex.I • euclideanComplexInclusion (AmbientResponse.completedVariation F uI hI y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    have huy := (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hy)
    ext k
    apply Complex.ext
    · simp [completedVariationComplex_re F h huy, uR, hR]
    · simp [completedVariationComplex_im F h huy, uI, hI]
  have hmetric := complexLinearizedMetric_of_eventuallyEq_quadratures F
    ((hWR.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hx))
    ((hWI.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hx)) hW
  -- The real theorem only uses its operator through the signed residual.
  -- Specializing its datum to minus the prescribed residual and its operator
  -- to zero lets us apply it to each quadrature of the actual complex equation.
  have hreal := AmbientResponse.completedVariation_error_eq_full_residual hs hF huR
    himm hrank hhR hx (hh.map Complex.re) hQ hspan
    (fun y j ↦ -(A z y j - z y j).re) 0 (by simpa using hphysicalRe)
  have himag := AmbientResponse.completedVariation_error_eq_full_residual hs hF huI
    himm hrank hhI hx (hh.map Complex.im) hQ hspan
    (fun y j ↦ -(A z y j - z y j).im) 0 (by simpa using hphysicalIm)
  have hgram : WKB.stressGram Q = JanetCartan.stressGram Q := rfl
  ext i j
  apply Complex.ext
  · have hr := congrArg (fun M : MetricTensor n ↦ M i j) hreal
    simpa [WKB.stressReconstruction, hgram,
      Matrix.sum_apply, hR, (hmetric i j).1] using hr
  · have hi := congrArg (fun M : MetricTensor n ↦ M i j) himag
    simpa [WKB.stressReconstruction, hgram,
      Matrix.sum_apply, hI, (hmetric i j).2] using hi

end JanetCartan.ResponseTransfer
