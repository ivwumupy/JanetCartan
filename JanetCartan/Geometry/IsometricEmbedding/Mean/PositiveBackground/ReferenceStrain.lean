module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.CovectorRaising

/-!
# The constant reference strain

The reference calculation in `app:ch_background:prop:bg-positive`:
for `X₀(x) = -H₀ x / 2` and `γ(G) = I`, the actual linearized metric
of `dG X₀` is `-H₀`. No assertion about the zero-scale immersion is used.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.PositiveBackground

variable {n N : ℕ}

/-- `app:ch_background:prop:bg-positive`: the linear reference field `-H₀ x / 2`. -/
def referenceVectorField (H₀ : MetricTensor n) : Euclidean n →L[ℝ] Euclidean n :=
  (-1 / 2 : ℝ) • H₀.toEuclideanLin.toContinuousLinearMap

/-- `app:ch_background:prop:bg-positive`: the reference field has constant
coordinate derivative with the prescribed factor `-1/2`. -/
theorem partialDeriv_referenceVectorField (H₀ : MetricTensor n) (x : Euclidean n)
    (i j : Fin n) :
    partialDeriv (fun y ↦ referenceVectorField H₀ y j) x i = (-1 / 2 : ℝ) * H₀ j i := by
  have h := ((EuclideanSpace.proj j).comp (referenceVectorField H₀)).fderiv
    (x := x)
  change fderiv ℝ ((EuclideanSpace.proj j).comp (referenceVectorField H₀)) x
    (EuclideanSpace.single i 1) = _
  rw [h]
  change (-1 / 2 : ℝ) * (∑ k, H₀ j k * (EuclideanSpace.single i 1) k) = _
  simp

/-- `app:ch_background:prop:bg-positive`: an identically Euclidean induced
metric has zero Christoffel coefficients on its open domain. -/
theorem christoffel_eq_zero_of_inducedMetric_one {G : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hflat : ∀ x ∈ U, inducedMetric G x = 1) {x : Euclidean n} (hx : x ∈ U)
    (i j k : Fin n) : christoffel G x i j k = 0 := by
  have hd (a b c : Fin n) : partialDeriv (fun y ↦ inducedMetric G y a b) x c = 0 := by
    have heq : (fun y ↦ inducedMetric G y a b) =ᶠ[nhds x]
        (fun _ ↦ (1 : MetricTensor n) a b) :=
      Filter.Eventually.mono (hU.mem_nhds hx) fun y hy ↦
        congrArg (fun M : MetricTensor n ↦ M a b) (hflat y hy)
    simp only [partialDeriv, heq.fderiv_eq, fderiv_const_apply, zero_apply]
  simp only [christoffel, hd, add_zero, sub_self, mul_zero, Finset.sum_const_zero]

/-- `app:ch_background:prop:bg-positive`: on a flat reference domain the
covariant strain of `X₀` is exactly `-H₀ / 2`. -/
theorem twice_symmCovariantDeriv_referenceVectorField {G : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hflat : ∀ x ∈ U, inducedMetric G x = 1)
    (H₀ : MetricTensor n) (hH₀ : H₀.IsSymm) {x : Euclidean n} (hx : x ∈ U) :
    2 • symmCovariantDeriv G (referenceVectorField H₀) x = -H₀ := by
  ext i j
  simp only [Matrix.smul_apply, symmCovariantDeriv,
    partialDeriv_referenceVectorField, christoffel_eq_zero_of_inducedMetric_one hU hflat hx,
    zero_mul, Finset.sum_const_zero, sub_zero, Matrix.neg_apply]
  rw [hH₀.apply j i]
  ring

/-- `app:ch_background:prop:bg-positive`: with metric `I`, raising a covector
does not change its coordinate vector. -/
theorem raisedCorrection_eq_of_inducedMetric_one {G : Euclidean n → Euclidean N}
    (u : Euclidean n → Euclidean n) {x : Euclidean n} (hflat : inducedMetric G x = 1) :
    raisedCorrection G u x = u x := by
  ext i
  change (∑ j, (inducedMetric G x)⁻¹ i j * u x j) = u x i
  simp [hflat, Matrix.one_apply]

/-- `app:ch_background:prop:bg-positive`: the constant reference mean is
cancelled by the actual strain of `dG(-H₀ x / 2)` on a flat immersion domain. -/
theorem linearizedMetric_referenceVectorField {G : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (himm : IsImmersionOn G U) (hflat : ∀ x ∈ U, inducedMetric G x = 1)
    (H₀ : MetricTensor n) (hH₀ : H₀.IsSymm) :
    EqOn (linearizedMetric G (tangentVariation G (referenceVectorField H₀)))
      (fun _ ↦ -H₀) U := by
  intro x hx
  have heq : tangentVariation G (referenceVectorField H₀) =ᶠ[nhds x]
      tangentLift G (referenceVectorField H₀) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← tangentVariation_raisedCorrection]
    exact congrArg (fderiv ℝ G y)
      (raisedCorrection_eq_of_inducedMetric_one _ (hflat y hy)).symm
  have hstrain := linearizedMetric_tangentLift hU hG
    (referenceVectorField H₀).contDiff.contDiffOn himm hx
  have hflatStrain := twice_symmCovariantDeriv_referenceVectorField hU hflat H₀ hH₀ hx
  calc
    linearizedMetric G (tangentVariation G (referenceVectorField H₀)) x =
        linearizedMetric G (tangentLift G (referenceVectorField H₀)) x := by
      ext i j
      unfold linearizedMetric partialDeriv
      rw [heq.fderiv_eq]
    _ = 2 • symmCovariantDeriv G (referenceVectorField H₀) x := hstrain
    _ = -H₀ := hflatStrain

end JanetCartan.PositiveBackground
