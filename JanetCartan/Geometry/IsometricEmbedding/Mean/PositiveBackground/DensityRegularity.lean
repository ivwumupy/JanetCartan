module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.DensityRepresentative
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.DensityBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.ContinuousDensity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.DensityNormalization
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Smooth factor-four density with uniform finite-jet bounds

The density in `app:ch_background:eq:bg-density-four` has one globally smooth
real representative whenever its raw input belongs to every full raw Sobolev
level. The checked uncut multiplier and smooth-representative estimates give
the global `cNorm` bounds with reserve `q = 3 + (n - 1) + 1`, including `n = 0`.
The constants precede the input, and the representative is shared by all orders.

The exact normalization is `2 * synthesisFactor n` times `densityUncutL2`.
Equality at every initial position for almost every carrier justifies the
transported mean. The external plateau product holds everywhere. All measures
and coordinates are the original ones; synthesis has no initial-position cutoff.

Consumers are `amplitude_properties_of_small_density`,
`uncorrectedDensity_core_cancellation`, and the profile estimate
`app:ch_background:eq:bg-positive-profile`. The actual same-row inverse/adjoint
must still supply the all-order raw membership and small norm for its input.
This deduction does not complete `app:ch_background:prop:bg-positive`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.PositiveBackground

open ContinuumRow CarrierSobolev UncutDensity ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- The literal factor-four density has a uniform global derivative seminorm
bound, with a constant chosen before the raw input and valid for every smooth
representative (`app:ch_background:eq:bg-density-four`,
`app:ch_background:eq:bg-positive-profile`). -/
theorem exists_initialDensity_four_cNorm_bound (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hcρ : HasCompactSupport (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : CarrierL2 n), (∀ k : ℕ, MemRawSobolev k u) →
      ∀ (v : CarrierVariable n → ℝ), ContDiff ℝ ∞ v →
      v =ᵐ[carrierMeasure n] initialDensity d 4 u →
      cNorm univ s v ≤ C * rawSobolevNorm (s + (3 + (n - 1) + 1) + 1) u := by
  obtain ⟨C, hC, hb⟩ := CurrentMean.exists_initialDensityRepresentative_derivative_bound
    d hρsmooth hcρ hχsmooth hlow hχ hA hρ 4 s
  refine ⟨(s + 1 : ℕ) * C, by positivity, ?_⟩
  intro u hu v hv he
  have hnorm : 0 ≤ rawSobolevNorm (s + (3 + (n - 1)) + 1 + 1) u :=
    ENNReal.toReal_nonneg
  have h := cNorm_le_sum_of_bounds (s := univ) (r := s) (f := v)
    (fun _ _ ↦ mul_nonneg hC hnorm) (fun j hj p _ ↦ hb u hu v hv he j hj p)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.add_assoc,
    mul_assoc] using h

/-- Construct ONE smooth real factor-four density for all derivative orders.
The constants are chosen before the raw input; the reserve depends only on the
dimension (`app:ch_background:eq:bg-density-four`,
`app:ch_background:eq:bg-positive-profile`). Full raw regularity is the precise
remaining input obligation of the same-row inverse/adjoint construction. -/
theorem exists_smooth_initialDensity_four_cNorm (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hcρ : HasCompactSupport (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (u : CarrierL2 n), (∀ k : ℕ, MemRawSobolev k u) →
        ∃ v : CarrierVariable n → ℝ, ContDiff ℝ ∞ v ∧
          v =ᵐ[carrierMeasure n] initialDensity d 4 u ∧
          ∀ s, cNorm univ s v ≤ C s * rawSobolevNorm (s + (3 + (n - 1) + 1) + 1) u := by
  choose C hC hb using exists_initialDensity_four_cNorm_bound
    d hρsmooth hcρ hχsmooth hlow hχ hA hρ
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨v, hv, he⟩ := CurrentMean.exists_smooth_initialDensity
    d hρsmooth hcρ hχsmooth hlow hχ hA hρ 4 u hu
  exact ⟨v, hv, he, fun s ↦ hb s u hu v hv he⟩

/-- The smooth factor-four density retains exact multiplier normalization,
all initial positions, the measured mean, and every external carrier plateau
(`app:ch_background:eq:bg-density-four`, `app:ch_background:prop:bg-positive`).
The all-position equality is established before any footpoint substitution.
This supplies the density inputs for `uncorrectedDensity_core_cancellation`;
it assumes neither positivity nor successful background construction. -/
theorem exists_smooth_initialDensity_four (d : CarrierData n N)
    (hρsmooth : ContDiff ℝ ∞ (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hcρ : HasCompactSupport (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ContDiff ℝ ∞ d.highCutoff)
    (hlow : ∀ r ≤ 1, d.highCutoff r = 0)
    (hχ : ∀ r, |d.highCutoff r| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (u : CarrierL2 n) (hu : ∀ k : ℕ, MemRawSobolev k u),
        ∃ v : CarrierVariable n → ℝ, ContDiff ℝ ∞ v ∧
          v =ᵐ[carrierMeasure n] initialDensity d 4 u ∧
          (∀ s, cNorm univ s v ≤ C s * rawSobolevNorm (s + (3 + (n - 1) + 1) + 1) u) ∧
          v =ᵐ[carrierMeasure n] ((2 * synthesisFactor n) •
            densityUncutL2 hρsmooth.continuous.measurable hχsmooth.continuous.measurable
              hA (fun z θ _ ↦ by simpa using hρ z θ) hχ (hlow 0 zero_le_one) u
              (carrierWeightedMem_of_memRawSobolev (hu 1)) : Lp ℝ 2 (carrierMeasure n)) ∧
          (∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
            ∀ y, v (z, y) = initialDensity d 4 u (z, y)) ∧
          (∀ ψ : CarrierParameter → ℝ,
            measuredIncrement d ψ v = measuredIncrement d ψ (initialDensity d 4 u)) ∧
          (∀ (χ : CarrierParameter → ℝ), Continuous χ →
            (∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1) →
            ∀ p, χ p.1 ^ 2 * v p = v p) := by
  obtain ⟨C, hC, hb⟩ := exists_smooth_initialDensity_four_cNorm
    d hρsmooth hcρ hχsmooth hlow hχ hA hρ
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨v, hv, he, hbound⟩ := hb u hu
  have hpositions := initialDensity_eq_continuousRepresentative d (n + 1) (by omega)
    hρsmooth.continuous.measurable hχsmooth.continuous.measurable hA zero_le_one hρ hχ
    4 u (carrierWeightedMem_of_memRawSobolev (hu _)) hv.continuous he.symm
  refine ⟨v, hv, he, hbound, ?_, ?_, ?_, ?_⟩
  · exact he.trans (densityUncutL2_four_coeFn d (n + 1) (by omega)
      hρsmooth.continuous.measurable hχsmooth.continuous.measurable hA hρ hχ
      (hlow 0 zero_le_one) u (carrierWeightedMem_of_memRawSobolev (hu _))
      (carrierWeightedMem_of_memRawSobolev (hu 1))).symm
  · filter_upwards [hpositions] with z hz
    exact fun y ↦ (hz y).symm
  · intro ψ
    exact (measuredIncrement_continuousRepresentative d (n + 1) (by omega)
      hρsmooth.continuous.measurable hχsmooth.continuous.measurable hA zero_le_one hρ hχ
      4 u (carrierWeightedMem_of_memRawSobolev (hu _)) hv.continuous he.symm ψ).symm
  · intro χ hχc hplateau
    exact externalWeight_mul_continuousRepresentative d χ hχc hplateau 4 u hv.continuous he.symm

end JanetCartan.PositiveBackground
