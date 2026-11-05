module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# Fubini identity for the uncut transported density

The identities `app:ch_background:eq:bg-density-twice` and the carrier part of
`app:ch_mean_pairs:eq:mean-density-recursion`, on the literal integral domain.
Integrability of the original vector kernel is the only analytic hypothesis in
the Fubini calculation. It is not an assumed density/channel identity.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.UncutDensity

open ContinuumRow CarrierSobolev ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- Factor the existing kernel into its exact density symbol and measured
stress, without changing its phase (`app:ch_background:eq:bg-density-twice`). -/
theorem carrierKernel_factor (d : CarrierData n N) {x : Torus n}
    (hx : x ∈ d.outputChart) (u : CarrierVariable n) :
    carrierKernel d x u =
      (Complex.exp ((inner ℝ u.2 (d.transportedPosition (d.chartPoint x) u.1) : ℂ) *
        Complex.I) * carrierDensitySymbol d u) •
          euclideanComplexInclusion (measuredStress d x u.1) := by
  ext i
  simp [carrierKernel, hx, carrierAmplitude, carrierPhase, carrierDensitySymbol,
    densityFrequencySymbol, halfOrderCoefficient, angularHighMask, measuredStress,
    real_inner_comm, mul_comm Complex.I, mul_smul, Complex.real_smul,
    Complex.ofReal_pow]
  ring

/-- The transverse integral is precisely the unprefactored inverse synthesis
times the measured stress (`app:ch_background:eq:bg-density-twice`). -/
theorem integral_carrierKernel_slice (d : CarrierData n N) {x : Torus n}
    (hx : x ∈ d.outputChart) (f : CarrierVariable n → ℂ) (z : CarrierParameter) :
    (∫ η, f (z, η) • carrierKernel d x (z, η)) =
      radianInverseIntegral (fun η ↦ carrierDensitySymbol d (z, η) * f (z, η))
        (d.transportedPosition (d.chartPoint x) z) •
          euclideanComplexInclusion (measuredStress d x z) := by
  simp_rw [carrierKernel_factor d hx, smul_smul]
  rw [radianInverseIntegral, ← integral_smul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η ↦ by
    simp only [smul_eq_mul]
    congr 1
    ring

/-- Real part of scalar multiplication of a real stress vector, used in
`app:ch_background:eq:bg-density-twice`. -/
theorem realPart_smul_stress (a : ℂ) (v : Euclidean n) :
    euclideanRealPart (a • euclideanComplexInclusion v) = a.re • v := by
  ext i
  simp [Complex.mul_re]

/-- Fubini gives the measured density increment with its exact real coefficient.
The angular plateau is geometric data supplied by `jc-positive-background`;
the integrability input concerns the literal carrier integrand, not its output
identity (`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_initialDensity (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (c : ℝ) (f : CarrierVariable n → ℂ) (x : Torus n)
    (hf : Integrable (fun u ↦ f u • carrierKernel d x u) (carrierMeasure n)) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d c f) x =
      c • euclideanRealPart (carrierTestIntegral d f x) := by
  classical
  by_cases hx : x ∈ d.outputChart
  · rw [measuredIncrement, Set.indicator_of_mem hx]
    have he (z : CarrierParameter) :
        χ z ^ 2 * initialDensity d c f (z, d.transportedPosition (d.chartPoint x) z) =
          initialDensity d c f (z, d.transportedPosition (d.chartPoint x) z) :=
      externalWeight_mul_initialDensity d χ hχ c f
        (z, d.transportedPosition (d.chartPoint x) z)
    simp_rw [he]
    rw [carrierTestIntegral, carrierMeasure, integral_prod _ hf,
      ← euclideanRealPart.integral_comp_comm hf.integral_prod_left]
    simp_rw [integral_carrierKernel_slice d hx, realPart_smul_stress]
    simp only [initialDensity, mul_smul, integral_smul]
  · simp [measuredIncrement, hx, carrierTestIntegral_eq_zero_outside d f hx]

/-- The factor four in `app:ch_background:eq:bg-density-four` gives twice
the literal real carrier channel (`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_four (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (f : CarrierVariable n → ℂ) (x : Torus n)
    (hf : Integrable (fun u ↦ f u • carrierKernel d x u) (carrierMeasure n)) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d 4 f) x =
      (2 : ℝ) • ((2 : ℝ) • euclideanRealPart (carrierTestIntegral d f x)) := by
  rw [measuredIncrement_initialDensity d χ hχ 4 f x hf, smul_smul]
  norm_num

/-- The `-2 Re` specialization is minus the literal real carrier channel,
as required by `app:ch_mean_pairs:eq:mean-density-recursion`. -/
theorem measuredIncrement_neg_two (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (f : CarrierVariable n → ℂ) (x : Torus n)
    (hf : Integrable (fun u ↦ f u • carrierKernel d x u) (carrierMeasure n)) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d (-2) f) x =
      -((2 : ℝ) • euclideanRealPart (carrierTestIntegral d f x)) := by
  rw [measuredIncrement_initialDensity d χ hχ (-2) f x hf, neg_smul]

end JanetCartan.UncutDensity
