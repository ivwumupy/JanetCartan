module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ComplexWKB.Inverse
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Reduced.Formula
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.ActualReconstruction

/-!
# The concrete complex reduced operator and its WKB coefficients

The operator in `app:ch_waves:eq:reduced-symbol` is extended on both quadratures,
including its negative Christoffel contraction. The exact identification with
`WKB.firstOrderApply` and `WKB.principalSymbol` is consumed by the cubic residual
for `fullCorrectionCovector` in `ComplexWKB`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport GeometricProfile

variable {n N : ℕ}

/-- The actual first-order complex coefficient `C_a` of
`app:ch_waves:eq:reduced-symbol`. -/
def complexReducedDerivative (Q : Euclidean n → Fin n → MetricTensor n)
    (x : Euclidean n) (a : Fin n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  complexSymbolMap (principalCoefficient (Q x) a)

/-- The actual zeroth-order coefficient, including every induced Christoffel
term in `app:ch_waves:eq:reduced-symbol`. -/
def complexReducedValue (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (x : Euclidean n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  complexSymbolMap (reducedZerothCoefficient F (Q x) x)

/-- The coordinate formula for the full complex reduced operator in
`app:ch_waves:eq:reduced-symbol`. Its two quadratures are proved below to be
the published real covariant operator. -/
def complexReducedOperator (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (u : Euclidean n → EuclideanSpace ℂ (Fin n)) (x : Euclidean n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i ↦
    (∑ a, ∑ k, (principalCoefficient (Q x) a i k : ℂ) *
      partialDeriv (fun y ↦ u y k) x a) +
    ∑ k, (reducedZerothCoefficient F (Q x) x i k : ℂ) * u x k

/-- The coordinate covariant operator is the WKB first-order operator, on
the whole complex vector space (`app:ch_waves:eq:WKB-residual`). -/
theorem complexReducedOperator_eq_firstOrder (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) :
    complexReducedOperator F Q u x =
      WKB.firstOrderApply (complexReducedDerivative Q) (complexReducedValue F Q) u x := by
  have hd (a k : Fin n) : partialDeriv (fun y ↦ u y k) x a = partialDeriv u x a k :=
    congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single a 1))
      (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (u x) k).comp x hu.hasFDerivAt).fderiv)
  ext i
  simp [complexReducedOperator, WKB.firstOrderApply, complexReducedDerivative,
    complexReducedValue, complexSymbolMap, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, hd]

/-- The real quadrature is exactly `reducedOperator`, retaining the covariant
connection (`app:ch_waves:eq:reduced-symbol`). -/
theorem complexReducedOperator_re (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    (complexReducedOperator F Q u x i).re = reducedOperator F Q
      (fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).re)) x i := by
  have hd (a k : Fin n) :
      partialDeriv (fun y ↦ (u y k).re) x a =
        (partialDeriv (fun y ↦ u y k) x a).re :=
    congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single a 1))
      ((Complex.reCLM.hasFDerivAt.comp x
        ((differentiableAt_piLp 2).mp hu k).hasFDerivAt).fderiv)
  rw [reducedOperator_eq_coefficients F Q _ x hQ]
  simp [complexReducedOperator, Complex.mul_re, hd]

/-- The imaginary quadrature is the same real covariant operator, with no
projection onto the real channel (`app:ch_waves:eq:reduced-symbol`). -/
theorem complexReducedOperator_im (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hu : DifferentiableAt ℝ u x) (i : Fin n) :
    (complexReducedOperator F Q u x i).im = reducedOperator F Q
      (fun y ↦ WithLp.toLp 2 (fun k ↦ (u y k).im)) x i := by
  have hd (a k : Fin n) :
      partialDeriv (fun y ↦ (u y k).im) x a =
        (partialDeriv (fun y ↦ u y k) x a).im :=
    congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single a 1))
      ((Complex.imCLM.hasFDerivAt.comp x
        ((differentiableAt_piLp 2).mp hu k).hasFDerivAt).fderiv)
  rw [reducedOperator_eq_coefficients F Q _ x hQ]
  simp [complexReducedOperator, Complex.mul_im, hd]

/-- Real input gives the SAME real reduced operator under complex inclusion
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexReducedOperator_inclusion (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hQ : ∀ i, (Q x i).IsSymm) (hu : DifferentiableAt ℝ u x) :
    complexReducedOperator F Q (fun y ↦ euclideanComplexInclusion (u y)) x =
      euclideanComplexInclusion (WithLp.toLp 2 (reducedOperator F Q u x)) := by
  have hc : DifferentiableAt ℝ (fun y ↦ euclideanComplexInclusion (u y)) x :=
    euclideanComplexInclusion.differentiableAt.comp x hu
  ext i
  apply Complex.ext
  · simp only [complexReducedOperator_re F Q hQ hc, euclideanComplexInclusion_apply,
      Complex.ofReal_re, WithLp.toLp_ofLp]
  · simp only [complexReducedOperator_im F Q hQ hc, euclideanComplexInclusion_apply,
      Complex.ofReal_im]
    simp [reducedOperator, tensorPairing, symmCovariantDeriv, partialDeriv]

/-- The actual complex principal symbol is the complexification of
`reducedSymbol Q (dφ)`, with the same derivative convention
(`app:ch_waves:eq:reduced-symbol`). -/
theorem complexReduced_principalSymbol (Q : Euclidean n → Fin n → MetricTensor n)
    (φ : Euclidean n → ℝ) (x : Euclidean n) (hQ : ∀ i, (Q x i).IsSymm) :
    WKB.principalSymbol (complexReducedDerivative Q) φ x =
      complexSymbolMap (reducedSymbol (Q x) (gradient φ x)) := by
  rw [← LeadingWave.scalarDifferential_eq_gradient]
  apply LinearMap.ext
  intro v
  ext i
  simp only [WKB.principalSymbol, LinearMap.sum_apply, LinearMap.smul_apply,
    complexReducedDerivative, complexSymbolMap, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply, reducedSymbol,
    LeadingWave.scalarDifferential, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, principalCoefficient, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hQ i).apply k a]
  ring

end JanetCartan.RawPrimary
