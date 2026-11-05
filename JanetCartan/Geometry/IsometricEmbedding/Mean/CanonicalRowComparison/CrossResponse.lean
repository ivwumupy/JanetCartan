module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Matrix
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# The measured complex kernel of the real cross response

The literal polarization in `app:ch_mean_pairs:defn:mean-canonical` is
`C[2 sym Re(B* G)]`. Construct its complex-linear measured kernel from the
existing real measurement and Hermitian polarization, and commute it through
the actual finite annular integrals. The background is a separate uncut value;
the Fourier mask occurs only in the derivative integrand.

The consumer is the identification of the sampled kernel with the derivative
map supplied by `CanonicalAtomRealization`. No normal comparison is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison

open CurrentMean

variable {m n : Type*} [Fintype m] [Fintype n]

local instance : ContinuousENorm (Matrix m n ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix m n ℂ) inferInstance).toContinuousENorm

/-- The complex-linear measured cross kernel whose real channel is exactly
`C[2 sym Re(B* G)]` (`app:ch_mean_pairs:defn:mean-canonical`). The supplied
background `B` is independent of every Fourier input mask. -/
def complexCrossMeasurement (C : Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n)
    (B : Matrix m n ℂ) : Matrix m n ℂ →L[ℂ] EuclideanSpace ℂ n :=
  let L := C.comp (hermitianContinuousBilinear B)
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ euclideanComplexInclusion (L v) -
        Complex.I • euclideanComplexInclusion (L (Complex.I • v))
      map_add' := by
        intro u v
        simp only [smul_add, map_add]
        abel
      map_smul' := by
        intro a v
        have hdecomp (b : ℂ) : b • v = b.re • v + b.im • (Complex.I • v) := by
          ext i j
          change b * v i j = _
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
            Complex.real_smul, ← mul_assoc]
          rw [← add_mul]
          congr 1
          exact (Complex.re_add_im b).symm
        rw [hdecomp a]
        simp only [smul_add, map_add, map_smul, smul_comm Complex.I (a.re),
          smul_comm Complex.I (a.im), smul_smul, Complex.I_mul_I, neg_one_smul,
          map_neg]
        ext i
        apply Complex.ext <;> simp
        ring }

/-- Taking the real part of the constructed complex measurement gives the
original symmetric Hermitian cross tensor, with no change of measurement
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem complexCrossMeasurement_realPart
    (C : Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n) (B V : Matrix m n ℂ) :
    euclideanRealPart (complexCrossMeasurement C B V) =
      C (mixedHermitianTensor B V) := by
  ext i
  simp [complexCrossMeasurement]

/-- The real channel has factor two, before any normal or inverse is taken
(`main:eq:canonical-identity`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem twice_real_complexCrossMeasurement
    (C : Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n) (B V : Matrix m n ℂ) :
    (2 : ℝ) • euclideanRealPart (complexCrossMeasurement C B V) =
      C ((2 : ℝ) • mixedHermitianTensor B V) := by
  rw [complexCrossMeasurement_realPart, map_smul]

/-- Passing the fixed uncut background and measurement through the finite
annular synthesis proves the actual cross-response formula. Both quadratures,
all Fourier factors in `f`, and each ORIGINAL measure `μ i` are retained
(`app:ch_mean_pairs:defn:mean-canonical`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem measured_cross_sum_integral {ι X : Type*} [MeasurableSpace X]
    (s : Finset ι) (μ : ι → Measure X)
    (C : Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n) (B : Matrix m n ℂ)
    (f : ι → X → ℂ) (K : ι → X → Matrix m n ℂ)
    (hint : ∀ i ∈ s, Integrable (fun η ↦ f i η • K i η) (μ i)) :
    (2 : ℝ) • euclideanRealPart
        (∑ i ∈ s, ∫ η, f i η • complexCrossMeasurement C B (K i η) ∂μ i) =
      C ((2 : ℝ) • mixedHermitianTensor B
        (∑ i ∈ s, ∫ η, f i η • K i η ∂μ i)) := by
  have he : (∑ i ∈ s, ∫ η, f i η • complexCrossMeasurement C B (K i η) ∂μ i) =
      complexCrossMeasurement C B (∑ i ∈ s, ∫ η, f i η • K i η ∂μ i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [map_smul] using
      (complexCrossMeasurement C B).integral_comp_comm (hint i hi)
  rw [he, twice_real_complexCrossMeasurement]

end JanetCartan.CanonicalRowComparison
