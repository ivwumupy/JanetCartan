module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.CrossResponse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationSmooth
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude

/-!
# The transport cross amplitude is the original continuum coefficient

The zero endpoint in `app:ch_waves:eq:colored-normal-comparison` uses the
principal derivative matrix of the same normal and covector. Its complex
cross measurement is real and equals the coefficient in the original
`ContinuumRow.carrierKernel`. This identifies that coefficient before taking
adjoints or normals; no equality between independently chosen rows is assumed.

The measurement chart, stress frame and cutoff below are those of the supplied
`CarrierData`. Initial Fourier masks do not act on its background matrix.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison

open CurrentMean ContinuumRow LeadingWave

variable {m k : Type*} [Fintype m] [Fintype k]

omit [Fintype k] in
/-- The imaginary quadrature of a real principal matrix has zero symmetric
cross tensor with that matrix (`app:ch_background:eq:bg-realification`). -/
theorem mixedHermitianTensor_ofReal_I_self (A : Matrix m k ℝ) :
    mixedHermitianTensor (A.map Complex.ofReal) (Complex.I • A.map Complex.ofReal) = 0 := by
  have hre : (A.map Complex.ofReal).map Complex.re = A := by ext; simp
  have him : (A.map Complex.ofReal).map Complex.im = 0 := by ext; simp
  have hire : (Complex.I • A.map Complex.ofReal).map Complex.re = 0 := by ext; simp
  simp [mixedHermitianTensor, hre, him, hire]

/-- The complex cross coefficient at a real principal matrix is exactly the
complex inclusion of its measured self tensor. This is the zero endpoint
needed in `app:ch_waves:eq:colored-normal-comparison`. -/
theorem complexCrossMeasurement_ofReal_self
    (C : Matrix k k ℝ →L[ℝ] EuclideanSpace ℝ k) (A : Matrix m k ℝ) :
    complexCrossMeasurement C (A.map Complex.ofReal) (A.map Complex.ofReal) =
      euclideanComplexInclusion (C (Aᵀ * A)) := by
  change euclideanComplexInclusion (C (mixedHermitianTensor _ _)) -
    Complex.I • euclideanComplexInclusion (C (mixedHermitianTensor _ _)) = _
  rw [mixedHermitianTensor_ofReal_I_self, mixedHermitianTensor_self, hermitianTensor_ofReal]
  simp

/-- The same principal matrix gives the precise rank-one transport
coefficient of `app:ch_background:eq:bg-T`, with no polarization factor
absorbed into the amplitude. The real channel still supplies factor two. -/
theorem complexCrossMeasurement_principalMatrix {n N : ℕ}
    (C : MetricTensor n →L[ℝ] Euclidean n) (ν : Euclidean N) (ξ : Euclidean n) :
    complexCrossMeasurement C ((principalMatrix ν ξ).map Complex.ofReal)
        ((principalMatrix ν ξ).map Complex.ofReal) =
      euclideanComplexInclusion (C (fun i j ↦ ‖ν‖ ^ 2 * ξ i * ξ j)) := by
  rw [complexCrossMeasurement_ofReal_self, principalMatrix_transpose_mul]

/-- The original continuum kernel is exactly the oscillatory cross response
of its zero-input principal matrix, with the original detector, high-pass,
half derivative and output measurement. This is the literal coefficient
matching for `app:ch_waves:eq:colored-normal-comparison` and
`app:ch_mean_pairs:defn:mean-canonical`. -/
theorem carrierKernel_eq_principal_cross {n N : ℕ} (d : CarrierData n N)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel d x u =
      Complex.exp (Complex.I * (carrierPhase d x u : ℂ)) •
        (d.angularCutoff u.1 (‖u.2‖⁻¹ • u.2) * d.highCutoff ‖u.2‖ * Real.sqrt ‖u.2‖) •
          complexCrossMeasurement (preparationMeasurement d x)
            ((principalMatrix (d.normalField (d.chartPoint x) u.1)
              (d.covector (d.chartPoint x) u.1)).map Complex.ofReal)
            ((principalMatrix (d.normalField (d.chartPoint x) u.1)
              (d.covector (d.chartPoint x) u.1)).map Complex.ofReal) := by
  classical
  rw [complexCrossMeasurement_principalMatrix, preparationMeasurement_apply]
  by_cases hx : x ∈ d.outputChart
  · rw [carrierKernel, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have ht : (fun i j ↦ ‖d.normalField (d.chartPoint x) u.1‖ ^ 2 *
        d.covector (d.chartPoint x) u.1 i * d.covector (d.chartPoint x) u.1 j) =
        ‖d.normalField (d.chartPoint x) u.1‖ ^ 2 •
          (fun i j ↦ d.covector (d.chartPoint x) u.1 i *
            d.covector (d.chartPoint x) u.1 j) := by
      ext i j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [ht, map_smul, map_smul]
    congr 1
    change euclideanComplexInclusion (_ • reducedCovector d (d.chartPoint x)
      (d.covector (d.chartPoint x) u.1)) = _
    simp only [preparationStressMeasurement, LinearMap.coe_mk, AddHom.coe_mk,
      reducedCovector, map_smul, smul_smul]
    congr 1
    ring
  · simp only [carrierKernel_eq_zero_outside d hx, Set.indicator_of_notMem hx,
      map_zero, smul_zero]

end JanetCartan.CanonicalRowComparison
