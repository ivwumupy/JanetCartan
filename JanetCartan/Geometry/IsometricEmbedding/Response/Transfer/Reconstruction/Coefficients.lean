module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Field
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient

/-!
# Literal coefficients of the completed ambient variation

The coefficient maps in `app:ch_response:eq:response-reconstruction-grading`
are formed from the actual inverse metric, Christoffel symbols and canonical
normal inverse. Their bounds are separate from this algebraic identification.
The consumer is the demodulated reconstruction in
`app:ch_response:eq:response-graded-displacement`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ResponseTransfer

/-- Christoffel contraction in `app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionConnectionCoefficient {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : (Fin n → ℝ) →ₗ[ℝ] MetricTensor n where
  toFun v i j := ∑ k, christoffel F x i j k * v k
  map_add' v w := by ext i j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by ext i j; simp [Finset.mul_sum, mul_left_comm]

/-- The zeroth-order reconstruction coefficient, including the negative
Christoffel contribution (`app:ch_response:eq:response-reconstruction-grading`). -/
def reconstructionValueCoefficient {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : (Fin n → ℝ) →ₗ[ℝ] Euclidean N :=
  (∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j •
    (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)).smulRight (partialDeriv F x i)) -
    (AmbientResponse.canonicalNormalCompletion F x).comp (reconstructionConnectionCoefficient F x)

/-- Symmetric derivative coordinates in `app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionSymmetricDerivativeCoordinates (n : ℕ) :
    ((Fin n × Fin n) → ℝ) →ₗ[ℝ] MetricTensor n where
  toFun d i j := (d (i, j) + d (j, i)) / 2
  map_add' d e := by ext i j; simp only [Pi.add_apply, Matrix.add_apply]; ring
  map_smul' a d := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply]
    ring

/-- The first-order coefficient uses the symmetric derivative with factor
`1/2` (`app:ch_response:eq:response-reconstruction-grading`). Tensor coordinates
are indexed by pairs; the tensor itself has the existing Frobenius norm. -/
def reconstructionDerivativeCoefficient {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : ((Fin n × Fin n) → ℝ) →ₗ[ℝ] Euclidean N :=
  (AmbientResponse.canonicalNormalCompletion F x).comp (reconstructionSymmetricDerivativeCoordinates n)

/-- Tensor coordinates for `app:ch_response:eq:response-full-map`. -/
def reconstructionTensorCoordinates (n : ℕ) : ((Fin n × Fin n) → ℝ) →ₗ[ℝ] MetricTensor n where
  toFun h i j := h (i, j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The source coefficient is exactly `-N_G/2`, as in
`app:ch_response:eq:response-full-map`. -/
def reconstructionSourceCoefficient {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : ((Fin n × Fin n) → ℝ) →ₗ[ℝ] Euclidean N :=
  (- (1 / 2 : ℝ)) • (AmbientResponse.canonicalNormalCompletion F x).comp
    (reconstructionTensorCoordinates n)

/-- The same `completedVariation` is the literal first-order coefficient
formula, without assuming any ambient estimate
(`app:ch_response:eq:response-graded-displacement`). -/
theorem completedVariation_eq_coefficients {n N : ℕ}
    (F : Euclidean n → Euclidean N) (u : Euclidean n → Euclidean n)
    (h : MetricField n) (x : Euclidean n) :
    AmbientResponse.completedVariation F u h x =
      reconstructionValueCoefficient F x (fun j ↦ u x j) +
      reconstructionDerivativeCoefficient F x
        (fun ij ↦ partialDeriv (fun y ↦ u y ij.2) x ij.1) +
      reconstructionSourceCoefficient F x (fun ij ↦ h x ij.1 ij.2) := by
  have he : symmCovariantDeriv F u x =
      ((fun i j ↦ (partialDeriv (fun y ↦ u y j) x i +
        partialDeriv (fun y ↦ u y i) x j) / 2) : MetricTensor n) -
      (fun i j ↦ ∑ k, christoffel F x i j k * u x k) := rfl
  simp only [AmbientResponse.completedVariation, Pi.add_apply, he,
    reconstructionValueCoefficient, reconstructionDerivativeCoefficient,
    reconstructionSourceCoefficient, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.neg_apply, map_sub, map_smul, neg_smul,
    tangentLift, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, reconstructionConnectionCoefficient, reconstructionSymmetricDerivativeCoordinates,
    reconstructionTensorCoordinates, smul_eq_mul]
  abel

/-- Identification with the published second-jet formula, including the
source correction (`app:ch_response:eq:response-reconstruction-grading`). -/
theorem completedVariation_eq_reconstructionJetValue {n N : ℕ}
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {u : Euclidean n → Euclidean n} (hu : ContDiff ℝ ∞ u)
    (h : MetricField n) {x : Euclidean n}
    (hi : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    AmbientResponse.completedVariation F u h x =
      GeometricProfile.reconstructionJetValue (GeometricProfile.reconstructionJet F u x) -
        (1 / 2 : ℝ) • AmbientResponse.canonicalNormalCompletion F x (h x) := by
  rw [GeometricProfile.reconstructionJetValue_eq hF hu hi hrank,
    AmbientResponse.completedVariation_eq]
  rfl

/-- Complex-linear extension of a real coefficient on finite coordinates.
The output is the shared complex Euclidean Hilbert space, and both real
quadratures are retained (`app:ch_response:prop:response-ambient`). -/
def complexCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (T : (ι → ℝ) →ₗ[ℝ] Euclidean N) : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun z := ∑ i, z i • euclideanComplexInclusion (T (Pi.single i 1))
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, smul_smul]

private theorem coordinate_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    ∑ i, v i • Pi.single i (1 : ℝ) = v := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply]

/-- Real part of the complex coefficient is the original real coefficient
on the real quadrature (`app:ch_response:prop:response-ambient`). -/
theorem complexCoefficient_re {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (T : (ι → ℝ) →ₗ[ℝ] Euclidean N) (z : ι → ℂ) (k : Fin N) :
    (complexCoefficient T z k).re = T (fun i ↦ (z i).re) k := by
  rw [← coordinate_sum (fun i ↦ (z i).re), map_sum]
  simp [complexCoefficient, map_smul]

/-- Imaginary part is the same real map on the other quadrature
(`app:ch_response:prop:response-ambient`). -/
theorem complexCoefficient_im {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (T : (ι → ℝ) →ₗ[ℝ] Euclidean N) (z : ι → ℂ) (k : Fin N) :
    (complexCoefficient T z k).im = T (fun i ↦ (z i).im) k := by
  rw [← coordinate_sum (fun i ↦ (z i).im), map_sum]
  simp [complexCoefficient, map_smul]

end JanetCartan.ResponseTransfer
