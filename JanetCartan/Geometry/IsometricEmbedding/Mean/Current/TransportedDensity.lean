module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Preparation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Integration
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The transported part of the actual preparation discrepancy

For `app:ch_mean_pairs:prop:mean-coarse`, the original normal already contains
the positive base scalar. Multiplying that normal by `sqrt (1 + v(z,Y))`
therefore gives the transport amplitude of the SAME corrected scalar.
Its measured Hermitian square is affine in `v`; the linear term is exactly
`UncutDensity.measuredIncrement`, including the external carrier weight.

The compact carrier weights and continuous geometric coefficients below are
primitive inputs of the original carrier construction. No transported-density
identity or discrepancy estimate is assumed. This file does not construct the
corrected current atoms or the regularity of the original inverse.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

open ContinuumRow UncutDensity LeadingWave

variable {n N : ℕ} {ι : Type*}

/-- The literal initial scalar `r_F sqrt(1+v)` in
`app:ch_mean_pairs:prop:mean-coarse`, on all carrier and initial variables. -/
def preparationAmplitude (r v : ι → CarrierVariable n → ℝ) :
    ι → CarrierVariable n → ℝ :=
  fun a p ↦ positiveDensityAmplitude (r a p) (v a p)

/-- The original zero density gives precisely the original initial scalar
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
@[simp] theorem preparationAmplitude_zero (r : ι → CarrierVariable n → ℝ) :
    preparationAmplitude r 0 = r := by
  funext a p
  exact positiveDensityAmplitude_zero _

/-- No cutoff in the initial spatial variable is introduced by preparation;
outside the carrier support the initial scalar is unchanged
(`app:ch_mean_pairs:eq:mean-prepared-scalar`). -/
theorem preparationAmplitude_eq_off_carrier
    (r : ι → CarrierVariable n → ℝ) {K : ι → Set CarrierParameter}
    (v : smoothSupportedDensity n ι K) (a : ι) (z : CarrierParameter)
    (hz : z ∉ K a) (y : Euclidean (n - 1)) :
    preparationAmplitude r v.val a (z, y) = r a (z, y) := by
  simp only [preparationAmplitude, (v.property a).2 z hz y,
    positiveDensityAmplitude_zero]

/-- Smoothness of the actual modulated scalar on the positive class. Its
positivity must be supplied by the finite-reserve induction, not by applying
square-root smoothness to arbitrary densities
(`app:ch_mean_pairs:eq:mean-prepared-scalar`). -/
theorem contDiff_preparationAmplitude
    (r : ι → CarrierVariable n → ℝ) {K : ι → Set CarrierParameter}
    (v : smoothSupportedDensity n ι K) (hr : ∀ a, ContDiff ℝ ∞ (r a))
    (hv : ∀ a p, 0 < 1 + v.val a p) (a : ι) :
    ContDiff ℝ ∞ (preparationAmplitude r v.val a) :=
  (hr a).mul ((contDiff_const.add (v.property a).1).sqrt
    (fun p ↦ (hv a p).ne'))

/-- Exact initial-density normalization, with the original scalar retained
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationAmplitude_sq (r v : ι → CarrierVariable n → ℝ)
    (a : ι) (p : CarrierVariable n) (hv : 0 ≤ 1 + v a p) :
    preparationAmplitude r v a p ^ 2 = r a p ^ 2 * (1 + v a p) :=
  positiveDensityAmplitude_sq hv

/-- The original measurement contraction, with no response factor `1/2`,
at a point of the auxiliary torus (`app:ch_background:eq:bg-affine-mean`). -/
def preparationStressMeasurement (d : CarrierData n N) (x : Torus n) :
    MetricTensor n →ₗ[ℝ] Euclidean n where
  toFun H := d.measurementCutoff x •
    WithLp.toLp 2 (fun i ↦ tensorPairing (d.stressFrame (d.chartPoint x) i) H)
  map_add' H G := by
    ext i
    simp [tensorPairing, mul_add, Finset.sum_add_distrib]
  map_smul' c H := by
    ext i
    simp [tensorPairing, Finset.mul_sum, mul_left_comm]

/-- The actual transported derivative amplitude for a density change, using
the original normal and footpoint (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def densityTransportMatrix (d : CarrierData n N) (v : CarrierVariable n → ℝ)
    (x : Torus n) (z : CarrierParameter) : Matrix (Fin N) (Fin n) ℂ :=
  (principalMatrix
    (Real.sqrt (1 + v (z, d.transportedPosition (d.chartPoint x) z)) •
      d.normalField (d.chartPoint x) z)
    (d.covector (d.chartPoint x) z)).map Complex.ofReal

/-- Connection to the actual initial-scalar transport formula: if the original
normal has scalar `r(z,Y)`, the displayed matrix has scalar `r(z,Y) sqrt(1+v(z,Y))`.
The carrier owner supplies this factorization from its characteristic formula;
it is not inferred from unrelated choices of `d` and `r`
(`app:ch_waves:thm:leading`, `app:ch_mean_pairs:prop:mean-coarse`). -/
theorem densityTransportMatrix_eq_prepared_principal (d : CarrierData n N)
    (r v : CarrierVariable n → ℝ) (x : Torus n) (z : CarrierParameter)
    (ν : Euclidean N)
    (hν : d.normalField (d.chartPoint x) z =
      r (z, d.transportedPosition (d.chartPoint x) z) • ν) :
    densityTransportMatrix d v x z =
      (principalMatrix
        (positiveDensityAmplitude (r (z, d.transportedPosition (d.chartPoint x) z))
          (v (z, d.transportedPosition (d.chartPoint x) z)) • ν)
        (d.covector (d.chartPoint x) z)).map Complex.ofReal := by
  simp only [densityTransportMatrix, hν, smul_smul, positiveDensityAmplitude, mul_comm]

/-- The rank-one Hermitian calculation proves the transported density factor
for the SAME original normal (`app:ch_background:eq:bg-affine-mean`). -/
theorem measurement_densityTransportMatrix (d : CarrierData n N)
    (v : CarrierVariable n → ℝ) (x : Torus n) (z : CarrierParameter)
    (hv : 0 ≤ 1 + v (z, d.transportedPosition (d.chartPoint x) z)) :
    preparationStressMeasurement d x (hermitianTensor (densityTransportMatrix d v x z)) =
      (1 + v (z, d.transportedPosition (d.chartPoint x) z)) • measuredStress d x z := by
  rw [densityTransportMatrix, principalMatrix_hermitianTensor, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hv]
  ext i
  change d.measurementCutoff x *
    (∑ j, ∑ k, d.stressFrame (d.chartPoint x) i j k *
      ((1 + v (z, d.transportedPosition (d.chartPoint x) z)) *
        ‖d.normalField (d.chartPoint x) z‖ ^ 2 *
          d.covector (d.chartPoint x) z j * d.covector (d.chartPoint x) z k)) =
    (1 + v (z, d.transportedPosition (d.chartPoint x) z)) *
      ((d.measurementCutoff x * ‖d.normalField (d.chartPoint x) z‖ ^ 2) *
        ∑ j, ∑ k, d.stressFrame (d.chartPoint x) i j k *
          (d.covector (d.chartPoint x) z j * d.covector (d.chartPoint x) z k))
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The literal colored transport mean on the output chart; color masks are
only integrated, never differentiated (`app:ch_mean_pairs:prop:mean-coarse`). -/
def coloredTransportMean {κ : Type*} [Fintype κ]
    (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (mask : κ → CarrierParameter → ℝ) (v : CarrierVariable n → ℝ)
    (x : Torus n) : Euclidean n :=
  d.outputChart.indicator (fun x ↦ ∫ z, ∑ c, mask c z •
    (χ z ^ 2 • preparationStressMeasurement d x
      (hermitianTensor (densityTransportMatrix d v x z))) ∂(volume.prod volume)) x

/-- Partition of unity removes the colors from the transported term exactly.
This is an identity for the literal integrands and needs no estimates or
derivatives of masks (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem coloredTransportMean_eq_increment {κ : Type*} [Fintype κ]
    (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (mask : κ → CarrierParameter → ℝ) (hmask : ∀ z, ∑ c, mask c z = 1)
    (v : CarrierVariable n → ℝ) (hv : ∀ p, 0 ≤ 1 + v p) :
    coloredTransportMean d χ mask v =
      measuredIncrement d (fun z ↦ χ z ^ 2) (fun p ↦ 1 + v p) := by
  funext x
  classical
  by_cases hx : x ∈ d.outputChart
  · simp only [coloredTransportMean, measuredIncrement, Set.indicator_of_mem hx]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [measurement_densityTransportMatrix d v x z (hv _), ← Finset.sum_smul,
      hmask, one_smul, smul_smul]
  · simp [coloredTransportMean, measuredIncrement, hx]

section IntegrableDensity

variable (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hY : ∀ x, ContinuousOn (d.transportedPosition (d.chartPoint x)) (tsupport χ))
    (hS : ∀ x, ContinuousOn (measuredStress d x) (tsupport χ))

include hχ hχc hY hS

/-- The literal transported-density integrand is integrable. Compact support
is only in the external carrier weight; the initial spatial density is uncut
(`app:ch_background:eq:bg-affine-mean`). -/
theorem integrable_measuredDensity (v : CarrierVariable n → ℝ) (hv : Continuous v)
    (x : Torus n) : Integrable (fun z ↦
      (χ z ^ 2 * v (z, d.transportedPosition (d.chartPoint x) z)) •
        measuredStress d x z) (volume.prod volume) := by
  have hc := ((hχ.continuousOn.pow 2).mul
    (hv.comp_continuousOn (continuousOn_id.prodMk (hY x)))).smul (hS x)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (hc.integrableOn_compact' hχc (isClosed_tsupport χ).measurableSet)
  intro z hz
  by_contra h
  apply hz
  simp [image_eq_zero_of_notMem_tsupport h]

/-- The transport density is genuinely affine, with precisely the uncut
measured increment as its linear term. Integrability is derived from primitive
carrier data, rather than supplied as a desired mean identity
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem coloredTransportMean_sub_base {κ : Type*} [Fintype κ]
    (mask : κ → CarrierParameter → ℝ) (hmask : ∀ z, ∑ c, mask c z = 1)
    (v : CarrierVariable n → ℝ) (hv : Continuous v)
    (hpositive : ∀ p, 0 ≤ 1 + v p) :
    coloredTransportMean d χ mask v - coloredTransportMean d χ mask 0 =
      measuredIncrement d (fun z ↦ χ z ^ 2) v := by
  rw [coloredTransportMean_eq_increment d χ mask hmask v hpositive,
    coloredTransportMean_eq_increment d χ mask hmask 0 (by simp)]
  funext x
  classical
  by_cases hx : x ∈ d.outputChart
  · simp only [Pi.sub_apply, measuredIncrement, Set.indicator_of_mem hx, Pi.zero_apply,
      add_zero, mul_one]
    have hb := integrable_measuredDensity d χ hχ hχc hY hS (fun _ ↦ 1) continuous_const x
    have hd := integrable_measuredDensity d χ hχ hχc hY hS v hv x
    simp only [mul_one] at hb
    simp_rw [mul_add, mul_one, add_smul]
    rw [integral_add hb hd, add_sub_cancel_left]
  · simp [measuredIncrement, hx]

/-- Transported density as an actual linear map on supported smooth densities.
The codomain here is literal functions; smooth periodic realization is a separate
geometric obligation (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationTransportLinear {K : ι → Set CarrierParameter} (a : ι) :
    smoothSupportedDensity n ι K →ₗ[ℝ] (Torus n → Euclidean n) where
  toFun v := measuredIncrement d (fun z ↦ χ z ^ 2) (v.val a)
  map_add' v w := by
    funext x
    classical
    by_cases hx : x ∈ d.outputChart
    · simp only [measuredIncrement, Set.indicator_of_mem hx, Submodule.coe_add,
        Pi.add_apply, mul_add, add_smul]
      exact integral_add
        (integrable_measuredDensity d χ hχ hχc hY hS _ (v.property a).1.continuous x)
        (integrable_measuredDensity d χ hχ hχc hY hS _ (w.property a).1.continuous x)
    · simp [measuredIncrement, hx]
  map_smul' c v := by
    funext x
    classical
    by_cases hx : x ∈ d.outputChart
    · simp only [measuredIncrement, Set.indicator_of_mem hx, Submodule.coe_smul,
        Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      simp_rw [mul_left_comm (χ _ ^ 2) c, ← smul_smul]
      exact integral_smul c _
    · simp [measuredIncrement, hx]

end IntegrableDensity

end JanetCartan.CurrentMean
