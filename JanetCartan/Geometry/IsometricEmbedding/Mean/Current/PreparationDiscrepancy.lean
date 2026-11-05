module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.TransportedDensity

/-!
# The literal colored discrepancy before sampling

This is the current-minus-transport integral in
`app:ch_mean_pairs:eq:mean-density-lipschitz`. The current maps are evaluated
at `r_F sqrt(1+v)`; the transport term uses the SAME original normal and
footpoint as the uncut density update. The exact affine transport identity is
proved in `TransportedDensity`, not assumed here.

The current maps remain the maps to be supplied by `jc-corrected-atoms`.
Their carrier continuity is a primitive regularity input. Neither an estimate
for the discrepancy nor success of the preparation is an input. Smooth torus
realization and the finite-order bounds still require actual producer assembly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

open ContinuumRow UncutDensity

variable {n N : ℕ} {κ : Type*} [Fintype κ]

/-- The measured colored current mean at the literal corrected initial scalar
(`app:ch_mean_pairs:prop:mean-coarse`). The maps are the original current maps,
with a common algebraic extension if needed outside their smooth source space. -/
def coloredPreparationCurrentMean (d : CarrierData n N)
    (χ : CarrierParameter → ℝ) (mask : κ → CarrierParameter → ℝ)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : CarrierVariable n → ℝ) (x : Torus n) : Euclidean n :=
  d.outputChart.indicator (fun x ↦ ∫ z, ∑ c, mask c z •
    (χ z ^ 2 • preparationStressMeasurement d x
      (hermitianTensor (current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x)))
        ∂(volume.prod volume)) x

/-- The actual discrepancy integrand, retaining both Hermitian tensors under
the original measurement and carrier integral
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def coloredPreparationDiscrepancy (d : CarrierData n N)
    (χ : CarrierParameter → ℝ) (mask : κ → CarrierParameter → ℝ)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : CarrierVariable n → ℝ) (x : Torus n) : Euclidean n :=
  d.outputChart.indicator (fun x ↦ ∫ z, ∑ c, mask c z •
    (χ z ^ 2 • preparationStressMeasurement d x
      (hermitianTensor (current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x) -
        hermitianTensor (densityTransportMatrix d v x z))) ∂(volume.prod volume)) x

section Identification

variable (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (mask : κ → CarrierParameter → ℝ)
    (hm : ∀ c, Measurable (mask c)) (hm₀ : ∀ c z, 0 ≤ mask c z)
    (hmask : ∀ z, ∑ c, mask c z = 1)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))

include hχ hχc hm hm₀ hmask

set_option backward.isDefEq.respectTransparency false in
/-- Integrability of the actual current-square mean follows from continuous
current amplitudes and the original compact external carrier weight. The color
masks need only be measurable; no mesh derivatives enter
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem integrable_coloredPreparationCurrent
    (r v : CarrierVariable n → ℝ)
    (hcurrent : ∀ c x, Continuous (fun z ↦
      current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x))
    (x : Torus n) : Integrable (fun z ↦ ∑ c, mask c z •
      (χ z ^ 2 • preparationStressMeasurement d x
        (hermitianTensor (current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x))))
          (volume.prod volume) := by
  apply integrable_finsetSum
  intro c _
  have ht : Continuous (fun z ↦
      hermitianTensor (current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x)) := by
    simpa only [Function.comp_apply, hermitianContinuousBilinear_apply,
      mixedHermitianTensor_self] using
      ((hermitianContinuousBilinear.continuous.comp (hcurrent c x)).clm_apply (hcurrent c x))
  have hc := (hχ.pow 2).smul ((preparationStressMeasurement d x).continuous_of_finiteDimensional.comp ht)
  have hs : HasCompactSupport (fun z ↦ χ z ^ 2) :=
    hχc.comp_left (g := fun a : ℝ ↦ a ^ 2) (by norm_num)
  apply (hc.integrable_of_hasCompactSupport hs.smul_right).bdd_smul 1
    (hm c).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hm₀ c z)]
  exact (Finset.single_le_sum (fun j _ ↦ hm₀ j z) (Finset.mem_univ c)).trans_eq (hmask z)

variable (hY : ∀ x, ContinuousOn (d.transportedPosition (d.chartPoint x)) (tsupport χ))
    (hS : ∀ x, ContinuousOn (measuredStress d x) (tsupport χ))

include hY hS

/-- The discrepancy is exactly the measured current mean minus the transport
mean, for these SAME initial data. All integrability of the transported term
is derived from primitive continuity and compact carrier support
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem coloredPreparationDiscrepancy_eq_sub (r v : CarrierVariable n → ℝ)
    (hv : Continuous v) (hpositive : ∀ p, 0 ≤ 1 + v p)
    (hcurrent : ∀ c x, Continuous (fun z ↦
      current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x)) :
    coloredPreparationDiscrepancy d χ mask current r v =
      coloredPreparationCurrentMean d χ mask current r v - coloredTransportMean d χ mask v := by
  funext x
  classical
  by_cases hx : x ∈ d.outputChart
  · have hT : Integrable (fun z ↦ ∑ c, mask c z •
        (χ z ^ 2 • preparationStressMeasurement d x
          (hermitianTensor (densityTransportMatrix d v x z)))) (volume.prod volume) := by
      have heq : (fun z ↦ ∑ c, mask c z •
          (χ z ^ 2 • preparationStressMeasurement d x
            (hermitianTensor (densityTransportMatrix d v x z)))) =
          (fun z ↦ (χ z ^ 2 * (1 + v (z, d.transportedPosition (d.chartPoint x) z))) •
            measuredStress d x z) := by
        funext z
        rw [measurement_densityTransportMatrix d v x z (hpositive _),
          ← Finset.sum_smul, hmask, one_smul, smul_smul]
      rw [heq]
      exact integrable_measuredDensity d χ hχ hχc hY hS _ (continuous_const.add hv) x
    simp only [coloredPreparationDiscrepancy, coloredPreparationCurrentMean,
      coloredTransportMean, Pi.sub_apply, Set.indicator_of_mem hx]
    simp_rw [map_sub, smul_sub, Finset.sum_sub_distrib]
    exact integral_sub
      (integrable_coloredPreparationCurrent d χ hχ hχc mask hm hm₀ hmask current r v hcurrent x) hT
  · simp [coloredPreparationDiscrepancy, coloredPreparationCurrentMean, coloredTransportMean, hx]

/-- The exact transport contribution in the preparation ledger is the original
uncut density synthesis. This closes the transported-square identity needed
before applying `BackgroundPreparation.run_residual_ledger`
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem coloredPreparationDiscrepancy_add_density (r v : CarrierVariable n → ℝ)
    (hv : Continuous v) (hpositive : ∀ p, 0 ≤ 1 + v p)
    (hcurrent : ∀ c x, Continuous (fun z ↦
      current c z (fun p ↦ positiveDensityAmplitude (r p) (v p)) x)) :
    coloredPreparationDiscrepancy d χ mask current r v +
        measuredIncrement d (fun z ↦ χ z ^ 2) v =
      coloredPreparationCurrentMean d χ mask current r v - coloredTransportMean d χ mask 0 := by
  rw [coloredPreparationDiscrepancy_eq_sub d χ hχ hχc mask hm hm₀ hmask current
    hY hS r v hv hpositive hcurrent,
    ← coloredTransportMean_sub_base d χ hχ hχc hY hS mask hmask v hv hpositive]
  abel

end Identification

section FiniteFamily

variable {ι : Type*} [Fintype ι]

/-- The full preparation discrepancy sums the literal carrier patches before
any sample is chosen (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def finitePreparationDiscrepancy (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (mask : ι → κ → CarrierParameter → ℝ)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : ι → CarrierVariable n → ℝ) : Torus n → Euclidean n :=
  ∑ a, coloredPreparationDiscrepancy (d a) (χ a) (mask a) (current a) (r a) (v a)

/-- The literal discrepancy has the original measurement-chart support.
There is no new cutoff between preparation steps
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem finitePreparationDiscrepancy_zero_off_chart (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (mask : ι → κ → CarrierParameter → ℝ)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : ι → CarrierVariable n → ℝ) {x : Torus n}
    (hx : ∀ a, x ∉ (d a).outputChart) :
    finitePreparationDiscrepancy d χ mask current r v x = 0 := by
  simp [finitePreparationDiscrepancy, coloredPreparationDiscrepancy, hx]

/-- The full linear transported-density map on the actual supported smooth
space (`app:ch_mean_pairs:eq:mean-density-recursion`). Each patch keeps its
original external carrier weight and transported footpoint. -/
def finitePreparationTransport (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a, Continuous (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    (hY : ∀ a x, ContinuousOn ((d a).transportedPosition ((d a).chartPoint x))
      (tsupport (χ a)))
    (hS : ∀ a x, ContinuousOn (measuredStress (d a) x) (tsupport (χ a)))
    (K : ι → Set CarrierParameter) :
    smoothSupportedDensity n ι K →ₗ[ℝ] (Torus n → Euclidean n) :=
  ∑ a, preparationTransportLinear (d a) (χ a) (hχ a) (hχc a) (hY a) (hS a) a

/-- For the full finite family, discrepancy plus the original affine density
term is exactly current mean minus original transport mean. This is the
same-data identification consumed by the finite preparation ledger; it assumes
no density/channel cancellation or discrepancy bound
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem finitePreparationDiscrepancy_add_transport
    (d : ι → CarrierData n N) (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a, Continuous (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    (hY : ∀ a x, ContinuousOn ((d a).transportedPosition ((d a).chartPoint x))
      (tsupport (χ a)))
    (hS : ∀ a x, ContinuousOn (measuredStress (d a) x) (tsupport (χ a)))
    (mask : ι → κ → CarrierParameter → ℝ)
    (hm : ∀ a c, Measurable (mask a c)) (hm₀ : ∀ a c z, 0 ≤ mask a c z)
    (hmask : ∀ a z, ∑ c, mask a c z = 1)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r : ι → CarrierVariable n → ℝ) {K : ι → Set CarrierParameter}
    (v : smoothSupportedDensity n ι K) (hpositive : ∀ a p, 0 ≤ 1 + v.val a p)
    (hcurrent : ∀ a c x, Continuous (fun z ↦ current a c z
      (preparationAmplitude r v.val a) x)) :
    finitePreparationDiscrepancy d χ mask current r v.val +
        finitePreparationTransport d χ hχ hχc hY hS K v =
      (∑ a, coloredPreparationCurrentMean (d a) (χ a) (mask a) (current a) (r a) (v.val a)) -
        ∑ a, coloredTransportMean (d a) (χ a) (mask a) 0 := by
  simp only [finitePreparationDiscrepancy, finitePreparationTransport, LinearMap.sum_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact coloredPreparationDiscrepancy_add_density (d a) (χ a) (hχ a) (hχc a)
    (mask a) (hm a) (hm₀ a) (hmask a) (current a) (hY a) (hS a) (r a) (v.val a)
    (v.property a).1.continuous (hpositive a) (hcurrent a)

end FiniteFamily

end JanetCartan.CurrentMean
