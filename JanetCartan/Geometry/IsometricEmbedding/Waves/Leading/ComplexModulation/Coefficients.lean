module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Complex
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator

/-!
# Actual complex coefficients of the leading reconstruction

Identify the zero-source `ResponseTransfer.completedVariationComplex` with
`LeadingWave.reconstruction F (canonicalNormalCompletion F)` on both quadratures.
Its actual first-order coefficients and principal symbol connect
`app:ch_waves:eq:reconstruction` and `app:ch_waves:eq:arbitrary-b-amplitudes`
to the existing WKB operator API. The symmetrization keeps its factor `1/2`,
and all tensors use the shared Frobenius convention.

The consumer is `Leading.ComplexModulation` and the actual leading-wave
construction. These coefficient identities require no characteristic, transport,
normal-rank, inverse-chart, or analytic-estimate assumptions.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.AmbientResponse JanetCartan.ResponseTransfer

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.LeadingWave

/-- The zero-source real response is exactly the canonical reconstruction of
`app:ch_waves:eq:reconstruction`; no inverse or regularity hypothesis is needed. -/
theorem completedVariation_zero_eq_reconstruction {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) :
    completedVariation F u 0 = reconstruction F (canonicalNormalCompletion F) u := by
  funext x
  simp [completedVariation, reconstruction, normalCorrection]

/-- The real quadrature of the actual zero-source response is the canonical
reconstruction in `app:ch_waves:eq:reconstruction`. -/
theorem completedVariationComplex_zero_re {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (k : Fin N) :
    (completedVariationComplex F u 0 x k).re =
      reconstruction F (canonicalNormalCompletion F)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ (u y j).re)) x k := by
  rw [completedVariationComplex_re F 0 hu]
  change completedVariation F _ 0 x k = _
  simp [completedVariation, reconstruction, normalCorrection]

/-- The imaginary quadrature uses the same canonical reconstruction in
`app:ch_waves:eq:reconstruction`, including for the complex WKB correction. -/
theorem completedVariationComplex_zero_im {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (k : Fin N) :
    (completedVariationComplex F u 0 x k).im =
      reconstruction F (canonicalNormalCompletion F)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ (u y j).im)) x k := by
  rw [completedVariationComplex_im F 0 hu]
  change completedVariation F _ 0 x k = _
  simp [completedVariation, reconstruction, normalCorrection]

/-- The complex zero-source operator on a real amplitude is the shared
inclusion of its canonical real reconstruction (`app:ch_waves:eq:reconstruction`). -/
theorem completedVariationComplex_zero_inclusion {n N : ℕ}
    (F : Euclidean n → Euclidean N) {b : Euclidean n → Euclidean n} {x : Euclidean n}
    (hb : DifferentiableAt ℝ b x) :
    completedVariationComplex F (fun y ↦ euclideanComplexInclusion (b y)) 0 x =
      euclideanComplexInclusion (reconstruction F (canonicalNormalCompletion F) b x) := by
  have hc : DifferentiableAt ℝ (fun y ↦ euclideanComplexInclusion (b y)) x :=
    euclideanComplexInclusion.differentiableAt.comp x hb
  ext k
  apply Complex.ext
  · simp only [completedVariationComplex_zero_re F hc, euclideanComplexInclusion_apply,
      Complex.ofReal_re]
  · simp only [completedVariationComplex_zero_im F hc, euclideanComplexInclusion_apply,
      Complex.ofReal_im]
    change reconstruction F (canonicalNormalCompletion F) 0 x k = 0
    have hz : JanetCartan.symmCovariantDeriv F 0 x = 0 := by
      ext i j
      simp [JanetCartan.symmCovariantDeriv, partialDeriv]
    simp [reconstruction, normalCorrection, tangentLift, hz]

/-- The actual complex first-order coefficients of `app:ch_waves:eq:reconstruction`,
using the published symmetric derivative and canonical normal completion.
These are the coefficients supplied to `WKB.firstOrder_reconstruction_twoTermWave`. -/
def canonicalReconstructionDerivative {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (complexCoefficient (reconstructionDerivativeCoefficient F x)).comp
    ({ toFun := fun b ij ↦ if ij.1 = i then b ij.2 else 0
       map_add' := by intros; ext ij; by_cases h : ij.1 = i <;> simp [h]
       map_smul' := by intros; ext ij; simp [mul_ite] } :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n × Fin n → ℂ))

/-- The actual complex zeroth-order coefficient of `app:ch_waves:eq:reconstruction`,
including the tangential lift and negative Christoffel contribution.
This is the value coefficient supplied to `WKB.firstOrder_reconstruction_twoTermWave`. -/
def canonicalReconstructionValue {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (complexCoefficient (reconstructionValueCoefficient F x)).comp
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap

/-- Complex extension of the literal normal amplitude in
`app:ch_waves:eq:arbitrary-b-amplitudes`. The following quadrature identities
identify it with `principalNormal` for the actual canonical completion. -/
def canonicalPrincipalNormalComplex {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x ξ : Euclidean n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (complexCoefficient (reconstructionDerivativeCoefficient F x)).comp
    ({ toFun := fun b ij ↦ (ξ ij.1 : ℂ) * b ij.2
       map_add' := by intros; ext ij; simp [mul_add]
       map_smul' := by intros; ext ij; simp [mul_left_comm] } :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n × Fin n → ℂ))

/-- The real quadrature of the complex principal amplitude is the literal
normal amplitude of `app:ch_waves:eq:arbitrary-b-amplitudes`. -/
theorem canonicalPrincipalNormalComplex_re {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x ξ : Euclidean n) (b : EuclideanSpace ℂ (Fin n)) (k : Fin N) :
    (canonicalPrincipalNormalComplex F x ξ b k).re =
      principalNormal (canonicalNormalCompletion F x) ξ
        (WithLp.toLp 2 (fun j ↦ (b j).re)) k := by
  simp only [canonicalPrincipalNormalComplex, LinearMap.comp_apply, complexCoefficient_re,
    reconstructionDerivativeCoefficient, LinearMap.comp_apply, principalNormal]
  apply congrArg (fun t ↦ canonicalNormalCompletion F x t k)
  ext i j
  simp [reconstructionSymmetricDerivativeCoordinates,
    symmetricProduct, mul_comm]

/-- The imaginary quadrature is the same literal normal amplitude of
`app:ch_waves:eq:arbitrary-b-amplitudes`, retaining the WKB correction channel. -/
theorem canonicalPrincipalNormalComplex_im {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x ξ : Euclidean n) (b : EuclideanSpace ℂ (Fin n)) (k : Fin N) :
    (canonicalPrincipalNormalComplex F x ξ b k).im =
      principalNormal (canonicalNormalCompletion F x) ξ
        (WithLp.toLp 2 (fun j ↦ (b j).im)) k := by
  simp only [canonicalPrincipalNormalComplex, LinearMap.comp_apply, complexCoefficient_im,
    reconstructionDerivativeCoefficient, LinearMap.comp_apply, principalNormal]
  apply congrArg (fun t ↦ canonicalNormalCompletion F x t k)
  ext i j
  simp [reconstructionSymmetricDerivativeCoordinates,
    symmetricProduct, mul_comm]

/-- Real amplitudes embed as the literal canonical principal normal from
`app:ch_waves:eq:arbitrary-b-amplitudes`. -/
theorem canonicalPrincipalNormalComplex_inclusion {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x ξ b : Euclidean n) :
    canonicalPrincipalNormalComplex F x ξ (euclideanComplexInclusion b) =
      euclideanComplexInclusion (principalNormal (canonicalNormalCompletion F x) ξ b) := by
  ext k
  apply Complex.ext
  · simp only [canonicalPrincipalNormalComplex_re, euclideanComplexInclusion_apply,
      Complex.ofReal_re]
  · simp only [canonicalPrincipalNormalComplex_im, euclideanComplexInclusion_apply,
      Complex.ofReal_im]
    rw [show WithLp.toLp 2 (fun _ : Fin n ↦ (0 : ℝ)) = (0 : Euclidean n) by ext j; rfl]
    simpa only [zero_smul, PiLp.zero_apply] using
      congrArg (fun v : Euclidean N ↦ v k)
        (principalNormal_smul (canonicalNormalCompletion F x) ξ b (0 : ℝ))

/-- The principal symbol of the actual reconstruction coefficients is the
complex extension of `principalNormal` at `dS`, with the published factor `1/2`
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem canonicalReconstruction_principalSymbol {n N : ℕ} (F : Euclidean n → Euclidean N)
    (φ : Euclidean n → ℝ) (x : Euclidean n) :
    WKB.principalSymbol (canonicalReconstructionDerivative F) φ x =
      canonicalPrincipalNormalComplex F x (scalarDifferential φ x) := by
  apply LinearMap.ext
  intro b
  simp only [WKB.principalSymbol, LinearMap.sum_apply, LinearMap.smul_apply,
    canonicalReconstructionDerivative, canonicalPrincipalNormalComplex, LinearMap.comp_apply]
  simp only [← map_smul]
  rw [← map_sum]
  apply congrArg (complexCoefficient (reconstructionDerivativeCoefficient F x))
  ext ij
  simp [scalarDifferential, Finset.sum_apply,
    Pi.smul_apply]

/-- Identify the actual zero-source response with the first-order operator
used by `WKB.firstOrder_reconstruction_twoTermWave`. Only differentiability
of the input at this point is needed (`app:ch_waves:eq:reconstruction`). -/
theorem completedVariationComplex_zero_eq_firstOrder {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) :
    completedVariationComplex F u 0 x =
      WKB.firstOrderApply (canonicalReconstructionDerivative F)
        (canonicalReconstructionValue F) u x := by
  have hd (i j : Fin n) : partialDeriv (fun y ↦ u y j) x i =
      partialDeriv u x i j := by
    exact congrArg (fun L : Euclidean n →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1))
      (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (u x) j).comp x hu.hasFDerivAt).fderiv)
  simp only [completedVariationComplex, Pi.zero_apply, Matrix.zero_apply, ← Pi.zero_def,
    map_zero, add_zero,
    WKB.firstOrderApply, canonicalReconstructionDerivative, canonicalReconstructionValue,
    LinearMap.comp_apply]
  rw [← map_sum]
  rw [add_comm]
  congr 1
  apply congrArg (complexCoefficient (reconstructionDerivativeCoefficient F x))
  ext ij
  simp [Finset.sum_apply, hd]

/-- The published response amplitude at zero source splits into the literal
principal normal and the same reconstructed amplitude. This coefficient identity
supplies `completedVariationComplex_zero_modulated` for
`app:ch_waves:eq:exact-W-amplitude`. -/
theorem responseReconstructionAmplitude_zero {n N : ℕ}
    (F : Euclidean n → Euclidean N) (ρ : ℝ) (S : Euclidean n → ℝ)
    (b : Euclidean n → EuclideanSpace ℂ (Fin n)) (x : Euclidean n) :
    ResponseTransfer.reconstructionAmplitude F ρ S 0 b 0 x =
      (Complex.I * (ρ : ℂ)) •
        canonicalPrincipalNormalComplex F x (scalarDifferential S x) (b x) +
      completedVariationComplex F b 0 x := by
  have hd : (fun ij : Fin n × Fin n ↦
      waveFirstAmplitude ρ S (fun y ↦ b y ij.2) x (EuclideanSpace.single ij.1 1)) =
      (Complex.I * (ρ : ℂ)) •
        (fun ij ↦ (scalarDifferential S x ij.1 : ℂ) * b x ij.2) +
        (fun ij ↦ partialDeriv (fun y ↦ b y ij.2) x ij.1) := by
    ext ij
    simp [waveFirstAmplitude, scalarDifferential, partialDeriv,
      mul_assoc]
  simp only [ResponseTransfer.reconstructionAmplitude, hd, Pi.zero_apply,
    Complex.ofReal_zero, zero_smul, add_zero, map_add, map_smul,
    canonicalPrincipalNormalComplex, LinearMap.comp_apply,
    completedVariationComplex, Matrix.zero_apply, ← Pi.zero_def, map_zero, add_zero,
    LinearMap.coe_mk, AddHom.coe_mk]
  abel

end JanetCartan.LeadingWave
