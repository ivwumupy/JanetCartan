module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SourceInverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMeanCancellation

/-!
# The corrected carrier uses the original inverse density

Only the normal amplitude changes: the phase, footpoint, stress, measurement,
angular and high-frequency masks are retained literally. The physical mean
keeps the supplied external weight and product measure. These identities
connect `PhysicalMeanCancellation` to the corrected-positive row in
`app:ch_background:prop:bg-current`; no second density is chosen.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedPositiveInverse
open ContinuumRow PositiveBackground

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- Apply the SAME uncut density to the original transported normal. All other
fields, including every cutoff and the original footpoint, are unchanged
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:prop:bg-current`). -/
def correctedCarrierData (d : CarrierData n N) (v : CarrierVariable n → ℝ) :
    CarrierData n N :=
  { d with normalField := fun x z ↦
      Real.sqrt (1 + v (z, d.transportedPosition x z)) • d.normalField x z }

/-- Zero density gives the literal original carrier, so the uncorrected row
is the zero-density member of this SAME family (`app:ch_background:eq:bg-T`). -/
@[simp] theorem correctedCarrierData_zero (d : CarrierData n N) :
    correctedCarrierData d 0 = d := by
  simp [correctedCarrierData]

/-- The corrected normal square has the exact density multiplier, with no
change to the source scale (`app:ch_background:eq:bg-affine-mean`). -/
theorem correctedCarrierData_normal_sq (d : CarrierData n N)
    (v : CarrierVariable n → ℝ) (x : Euclidean n) (z : CarrierParameter)
    (hv : 0 ≤ 1 + v (z, d.transportedPosition x z)) :
    ‖(correctedCarrierData d v).normalField x z‖ ^ 2 =
      (1 + v (z, d.transportedPosition x z)) * ‖d.normalField x z‖ ^ 2 := by
  simp only [correctedCarrierData, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hv]

/-- The SAME physical mean and external measure are obtained from the corrected
normal. This identifies the mean already canceled by
`physicalDensityMean_uncorrected_core_cancellation` with the corrected row's
base mean (`app:ch_background:eq:bg-current-identity`). -/
theorem physicalDensityMean_corrected_zero (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (v : ι → CarrierVariable n → ℝ)
    (hv : ∀ i p, 0 ≤ 1 + v i p) :
    physicalDensityMean (fun i ↦ correctedCarrierData (d i) (v i)) χ 0 =
      physicalDensityMean d χ v := by
  rw [physicalDensityMean_zero, physicalDensityMean_eq_carrierMean d χ v hv]
  rfl

/-- The actual carrier kernel is multiplied by the SAME density at its original
transported footpoint. The measurement and angular/high masks remain inside
the kernel, and the carrier measure remains `dz dη`
(`app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-affine-mean`). -/
theorem carrierKernel_corrected (d : CarrierData n N) (v : CarrierVariable n → ℝ)
    (hv : ∀ p, 0 ≤ 1 + v p) (x : Torus n) (u : CarrierVariable n) :
    carrierKernel (correctedCarrierData d v) x u =
      (1 + v (u.1, d.transportedPosition (d.chartPoint x) u.1)) • carrierKernel d x u := by
  classical
  have hamp : carrierAmplitude (correctedCarrierData d v) x u =
      (1 + v (u.1, d.transportedPosition (d.chartPoint x) u.1)) •
        carrierAmplitude d x u := by
    unfold carrierAmplitude
    rw [correctedCarrierData_normal_sq d v _ _ (hv _), smul_smul]
    dsimp only [correctedCarrierData, reducedCovector]
    congr 1
    ring
  by_cases hx : x ∈ d.outputChart
  · simp only [carrierKernel, show (correctedCarrierData d v).outputChart =
        d.outputChart from rfl, Set.indicator_of_mem hx]
    rw [hamp, map_smul]
    change Complex.exp (Complex.I * (carrierPhase d x u : ℂ)) •
        ((1 + v (u.1, d.transportedPosition (d.chartPoint x) u.1)) •
          euclideanComplexInclusion (carrierAmplitude d x u)) = _
    exact smul_comm _ _ _
  · simp [carrierKernel, correctedCarrierData, hx]

/-- The uncut factor-four synthesis sees exactly the original masks even after
correcting the normal; it is not a second density synthesis
(`app:ch_background:eq:bg-density-four`). -/
theorem initialDensity_correctedCarrierData (d : CarrierData n N)
    (v : CarrierVariable n → ℝ) (c : ℝ) (u : CarrierVariable n → ℂ) :
    UncutDensity.initialDensity (correctedCarrierData d v) c u =
      UncutDensity.initialDensity d c u :=
  initialDensity_eq_of_masks _ _ rfl rfl c u

/-- A smooth representative of the original inverse density is retained exactly
by the squared positive scalar. The right side still uses the UNCORRECTED
inverse, including its original source and exterior cutoffs
(`app:ch_background:eq:bg-density-four`, `app:ch_background:prop:bg-positive`). -/
theorem positiveScalar_sq_ae_uncorrectedDensity
    (d : ι → CarrierData n N) (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n) (σ : ℝ)
    (v : ι → CarrierVariable n → ℝ)
    (he : ∀ i, v i =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual i)
    (hv : ∀ i p, 0 ≤ 1 + v i p) (i : ι) :
    (fun p ↦ positiveDensityAmplitude σ (v i p) ^ 2) =ᵐ[carrierMeasure n]
      fun p ↦ σ ^ 2 * (1 + uncorrectedDensity d image U ψ θ residual i p) := by
  filter_upwards [he i] with p hp
  rw [positiveDensityAmplitude_sq (hv i p), hp]

/-- The smooth representative keeps the original external-weight absorption
pointwise, although its identification with the synthesized density was only
almost everywhere. Thus passing to the corrected row changes neither the
external measure nor the density used by physical cancellation
(`app:ch_background:eq:bg-density-twice`). -/
theorem externalWeight_mul_same_density
    (d : ι → CarrierData n N) (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ i, Continuous (χ i))
    (hplateau : ∀ i z η, (d i).angularCutoff z η ≠ 0 → χ i z = 1)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ θ : C(Torus n, ℝ)) (residual : OutputL2 n)
    (v : ι → CarrierVariable n → ℝ) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (he : ∀ i, v i =ᵐ[carrierMeasure n] uncorrectedDensity d image U ψ θ residual i)
    (i : ι) (p : CarrierVariable n) : χ i p.1 ^ 2 * v i p = v i p := by
  let : (carrierMeasure n).IsOpenPosMeasure := by
    unfold carrierMeasure
    infer_instance
  have hae : (fun q : CarrierVariable n ↦ χ i q.1 ^ 2 * v i q) =ᵐ[carrierMeasure n]
      v i := by
    filter_upwards [he i] with q hq
    rw [hq]
    exact externalWeight_mul_uncorrectedDensity d χ hplateau image U ψ θ residual i q
  exact congrFun (Measure.eq_of_ae_eq hae
    (((hχ i).comp continuous_fst).pow 2 |>.mul (hv i).continuous) (hv i).continuous) p

end JanetCartan.CorrectedPositiveInverse
