module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationDiscrepancy
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Smooth realization of the literal preparation discrepancy

For `app:ch_mean_pairs:eq:mean-density-lipschitz`, integrate the actual measured
Hermitian difference using the original colored carrier measure. Bounded
measurable masks are absorbed in the measure only for the regularity proof;
the resulting representative is exactly the original pointwise integral.

The geometric measurement field and original current/transport amplitudes
still require their joint smooth extensions from the actual producers. No
smoothness, bound, or cancellation of the resulting discrepancy is assumed.
-/

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.CurrentMean
open ContinuumRow

variable {n : ℕ}

/-- Compact carrier integration preserves smooth periodic sources even for
merely measurable color masks. This supplies the regularity of the literal
preparation discrepancy in `app:ch_mean_pairs:eq:mean-density-lipschitz`;
no derivatives of the mesh-dependent masks enter. -/
theorem isSmoothPeriodic_preparationMaskedIntegral (mask : CarrierParameter → ℝ) (hm : Measurable mask)
    (hm0 : ∀ z, 0 ≤ mask z) (hm1 : ∀ z, mask z ≤ 1)
    (f : Torus n × CarrierParameter → Euclidean n) (hc : Continuous f)
    (hf : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      f (torusQuotient p.1, p.2)))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hs : ∀ x z, z ∉ K → f (x,z) = 0) :
    IsSmoothPeriodic (fun x ↦ ∫ z, mask z • f (x,z) ∂(volume.prod volume)) := by
  let μ : Measure CarrierParameter := volume.prod volume
  let ν : Measure CarrierParameter := μ.withDensity (fun z ↦ ENNReal.ofReal (mask z))
  have hν : ν ≤ μ := by
    calc
      _ ≤ μ.withDensity (fun _ ↦ 1) := withDensity_mono
        (ae_of_all _ (fun z ↦ by simpa using ENNReal.ofReal_le_ofReal (hm1 z)))
      _ = μ := withDensity_one
  let : IsFiniteMeasureOnCompacts ν := ⟨fun _ h ↦ lt_of_le_of_lt (hν _) h.measure_lt_top⟩
  have heq (x : Torus n) : (∫ z, f (x,z) ∂ν) =
      ∫ z, mask z • f (x,z) ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hm0 _)]
  have hcont : Continuous (fun x : Torus n ↦ ∫ z, f (x,z) ∂ν) := by
    let : IsFiniteMeasure (ν.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    have hset : (fun x : Torus n ↦ ∫ z, f (x,z) ∂ν) =
        (fun x ↦ ∫ z in K, f (x,z) ∂ν) := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs x)).symm
    rw [hset]
    obtain ⟨C, hC⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hc.continuousOn
    apply continuous_of_dominated
      (fun x ↦ (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (fun x ↦ ?_) (integrable_const C)
      (ae_of_all _ (fun z ↦ hc.comp (continuous_id.prodMk continuous_const)))
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hC (x,z) ⟨mem_univ _,hz⟩
  have hdiff := FiniteChain.Retarded.KernelDecay.contDiff_integral_commonCarrier
    (μ := ν) hf hK (fun x z hz ↦ hs (torusQuotient x) z hz)
  refine ⟨?_, ?_⟩
  · simpa only [heq] using hcont
  · simpa only [periodicLift, Function.comp_def, heq] using hdiff



variable {N : ℕ} {κ : Type*} [Fintype κ]

/-- The original cutoff stress measurement, extended by zero off its chart
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
def preparationMeasurement (d : CarrierData n N) (x : Torus n) :
    MetricTensor n →L[ℝ] Euclidean n :=
  d.outputChart.indicator (fun y ↦
    (preparationStressMeasurement d y).toContinuousLinearMap) x

/-- Move the original measurement-chart indicator through its linear
contraction, without changing any physical cutoff
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationMeasurement_apply (d : CarrierData n N) (x : Torus n)
    (H : MetricTensor n) :
    preparationMeasurement d x H =
      d.outputChart.indicator (fun y ↦ preparationStressMeasurement d y H) x := by
  classical
  by_cases hx : x ∈ d.outputChart <;> simp [preparationMeasurement, hx]

/-- The literal colored discrepancy equals the integral with the original
measurement extended by zero. This equality precedes all regularity estimates
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem coloredPreparationDiscrepancy_eq_measuredIntegral
    (d : CarrierData n N) (χ : CarrierParameter → ℝ)
    (mask : κ → CarrierParameter → ℝ)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : CarrierVariable n → ℝ) (x : Torus n) :
    coloredPreparationDiscrepancy d χ mask current r v x =
      ∫ z, ∑ c, mask c z • (χ z ^ 2 • preparationMeasurement d x
        (hermitianTensor (current c z
          (fun p ↦ positiveDensityAmplitude (r p) (v p)) x) -
        hermitianTensor (densityTransportMatrix d v x z))) ∂(volume.prod volume) := by
  classical
  by_cases hx : x ∈ d.outputChart <;>
    simp [coloredPreparationDiscrepancy, preparationMeasurement, hx]

/-- Joint smoothness of the unmasked measured Hermitian difference is
inherited from its actual amplitude and coefficient fields
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem preparationHermitianIntegrand_regular
    (C : Torus n → MetricTensor n →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (χ : CarrierParameter → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (U T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hUc : Continuous U) (hTc : Continuous T)
    (hU : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      U (torusQuotient p.1, p.2)))
    (hT : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T (torusQuotient p.1, p.2))) :
    Continuous (fun p : Torus n × CarrierParameter ↦
      χ p.2 ^ 2 • C p.1 (hermitianTensor (U p) - hermitianTensor (T p))) ∧
    ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      χ p.2 ^ 2 • C (torusQuotient p.1)
        (hermitianTensor (U (torusQuotient p.1, p.2)) -
          hermitianTensor (T (torusQuotient p.1, p.2)))) := by
  have hUc' := (hermitianContinuousBilinear.continuous.comp hUc).clm_apply hUc
  have hTc' := (hermitianContinuousBilinear.continuous.comp hTc).clm_apply hTc
  have hU' := (hermitianContinuousBilinear.contDiff.comp hU).clm_apply hU
  have hT' := (hermitianContinuousBilinear.contDiff.comp hT).clm_apply hT
  simp only [Function.comp_apply, hermitianContinuousBilinear_apply,
    mixedHermitianTensor_self] at hUc' hTc' hU' hT'
  exact ⟨((hχ.continuous.comp continuous_snd).pow 2).smul
      ((hC.1.comp continuous_fst).clm_apply (hUc'.sub hTc')),
    ((hχ.comp contDiff_snd).pow 2).smul
      ((hC.2.comp contDiff_fst).clm_apply (hU'.sub hT'))⟩

/-- The SAME colored discrepancy is smooth periodic. The smooth extensions
of the original wave fields need agree only on the original measurement chart
and carrier support: a centered torus representative is not globally smooth.
The color masks are merely measurable and bounded by their partition of unity
(`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem isSmoothPeriodic_coloredPreparationDiscrepancy_of_extensions
    (d : CarrierData n N) (hC : IsSmoothPeriodic (preparationMeasurement d))
    (χ : CarrierParameter → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (mask : κ → CarrierParameter → ℝ)
    (hm : ∀ c, Measurable (mask c)) (hm₀ : ∀ c z, 0 ≤ mask c z)
    (hmask : ∀ z, ∑ c, mask c z = 1)
    (current : κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : CarrierVariable n → ℝ)
    (U : κ → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (T : Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hUc : ∀ c, Continuous (U c)) (hTc : Continuous T)
    (hU : ∀ c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      U c (torusQuotient p.1, p.2)))
    (hT : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T (torusQuotient p.1, p.2)))
    (hcurrent : ∀ c x, x ∈ d.outputChart → ∀ z, χ z ≠ 0 →
      U c (x,z) = current c z (fun q ↦ positiveDensityAmplitude (r q) (v q)) x)
    (htransport : ∀ x, x ∈ d.outputChart → ∀ z, χ z ≠ 0 →
      T (x,z) = densityTransportMatrix d v x z) :
    IsSmoothPeriodic (coloredPreparationDiscrepancy d χ mask current r v) := by
  let f (c : κ) (p : Torus n × CarrierParameter) : Euclidean n :=
    χ p.2 ^ 2 • preparationMeasurement d p.1
      (hermitianTensor (U c p) - hermitianTensor (T p))
  have hreg (c : κ) := preparationHermitianIntegrand_regular
    (preparationMeasurement d) hC χ hχ (U c) T (hUc c) hTc (hU c) hT
  have hs (c : κ) (x : Torus n) (z : CarrierParameter) (hz : z ∉ tsupport χ) :
      f c (x,z) = 0 := by simp [f, image_eq_zero_of_notMem_tsupport hz]
  have hm1 (c : κ) (z : CarrierParameter) : mask c z ≤ 1 :=
    (Finset.single_le_sum (fun j _ ↦ hm₀ j z) (Finset.mem_univ c)).trans_eq (hmask z)
  have hsm (c : κ) : IsSmoothPeriodic (fun x ↦ ∫ z, mask c z • f c (x,z)
      ∂(volume.prod volume)) :=
    isSmoothPeriodic_preparationMaskedIntegral (mask c) (hm c) (hm₀ c) (hm1 c)
      (f c) (hreg c).1 (hreg c).2 hχc (hs c)
  have hint (c : κ) (x : Torus n) :
      Integrable (fun z ↦ mask c z • f c (x,z)) (volume.prod volume) := by
    have hfc : HasCompactSupport (fun z ↦ f c (x,z)) := by
      apply hχc.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ (isClosed_tsupport χ)
      intro z hz
      by_contra hh
      exact hz (hs c x z hh)
    apply (((hreg c).1.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      hfc).bdd_smul 1 (hm c).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hm₀ c z)] using hm1 c z
  have heq : coloredPreparationDiscrepancy d χ mask current r v =
      fun x ↦ ∑ c, ∫ z, mask c z • f c (x,z) ∂(volume.prod volume) := by
    funext x
    rw [coloredPreparationDiscrepancy_eq_measuredIntegral,
      ← integral_finsetSum _ (fun c _ ↦ hint c x)]
    apply integral_congr_ae
    filter_upwards [] with z
    apply Finset.sum_congr rfl
    intro c _
    by_cases hx : x ∈ d.outputChart
    · by_cases hz : χ z = 0
      · simp [f, hz]
      · simp only [f, hcurrent c x hx z hz, htransport x hx z hz]
    · simp [f, preparationMeasurement, hx]
  rw [heq]
  exact ⟨continuous_finsetSum _ (fun c _ ↦ (hsm c).1),
    ContDiff.sum (fun c _ ↦ (hsm c).2)⟩

section FiniteRepresentative

variable {ι : Type*} [Fintype ι]
    (d : ι → CarrierData n N) (hC : ∀ a, IsSmoothPeriodic (preparationMeasurement (d a)))
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    (mask : ι → κ → CarrierParameter → ℝ)
    (hm : ∀ a c, Measurable (mask a c)) (hm₀ : ∀ a c z, 0 ≤ mask a c z)
    (hmask : ∀ a z, ∑ c, mask a c z = 1)
    (current : ι → κ → CarrierParameter → (CarrierVariable n → ℝ) →ₗ[ℝ]
      (Torus n → Matrix (Fin N) (Fin n) ℂ))
    (r v : ι → CarrierVariable n → ℝ)
    (U : ι → κ → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (T : ι → Torus n × CarrierParameter → Matrix (Fin N) (Fin n) ℂ)
    (hUc : ∀ a c, Continuous (U a c)) (hTc : ∀ a, Continuous (T a))
    (hU : ∀ a c, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      U a c (torusQuotient p.1, p.2)))
    (hT : ∀ a, ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      T a (torusQuotient p.1, p.2)))
    (hcurrent : ∀ a c x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      U a c (x,z) = current a c z (fun q ↦ positiveDensityAmplitude (r a q) (v a q)) x)
    (htransport : ∀ a x, x ∈ (d a).outputChart → ∀ z, χ a z ≠ 0 →
      T a (x,z) = densityTransportMatrix (d a) (v a) x z)

include hC hχ hχc hm hm₀ hmask hUc hTc hU hT hcurrent htransport in
/-- The literal finite preparation discrepancy belongs to the SAME smooth
periodic space used by the finite recurrence, before a sample is chosen
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem isSmoothPeriodic_finitePreparationDiscrepancy_of_extensions :
    IsSmoothPeriodic (finitePreparationDiscrepancy d χ mask current r v) := by
  have h (a : ι) := isSmoothPeriodic_coloredPreparationDiscrepancy_of_extensions
    (d a) (hC a) (χ a) (hχ a) (hχc a) (mask a) (hm a) (hm₀ a) (hmask a)
    (current a) (r a) (v a) (U a) (T a) (hUc a) (hTc a) (hU a) (hT a)
    (hcurrent a) (htransport a)
  refine ⟨?_, ?_⟩
  · apply (continuous_finsetSum Finset.univ (fun a _ ↦ (h a).1)).congr
    intro x
    simp [finitePreparationDiscrepancy]
  · simpa only [periodicLift, Function.comp_def, finitePreparationDiscrepancy,
      Finset.sum_apply] using ContDiff.sum (s := Finset.univ) (fun a _ ↦ (h a).2)

/-- The actual finite discrepancy as a smooth source. Its values are the
original integrals, not a newly selected L² representative
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationDiscrepancyRepresentative : SmoothResidual n :=
  ⟨fun x _ ↦ finitePreparationDiscrepancy d χ mask current r v x,
    fun _ ↦ isSmoothPeriodic_finitePreparationDiscrepancy_of_extensions
      d hC χ hχ hχc mask hm hm₀ hmask current r v U T hUc hTc hU hT hcurrent htransport⟩

/-- The discrepancy retains its original chart support, with no additional
source cutoff inserted between steps (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDiscrepancyRepresentative_supported :
    preparationDiscrepancyRepresentative d hC χ hχ hχc mask hm hm₀ hmask current
      r v U T hUc hTc hU hT hcurrent htransport ∈
      supportedSmoothResidual n (⋃ a, (d a).outputChart) := by
  intro x hx
  apply finitePreparationDiscrepancy_zero_off_chart
  intro a ha
  exact hx (mem_iUnion.mpr ⟨a, ha⟩)

/-- The L² input is the literal finite discrepancy almost everywhere. This
connects the next call to the SAME original `Q₀` to the measured current mean
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationDiscrepancyRepresentative_toL2 :
    smoothResidualToL2 n (preparationDiscrepancyRepresentative d hC χ hχ hχc mask hm
      hm₀ hmask current r v U T hUc hTc hU hT hcurrent htransport) =ᵐ[volume]
      finitePreparationDiscrepancy d χ mask current r v :=
  SmoothPeriodicFamily.componentL2_coe_ae () _

end FiniteRepresentative

end JanetCartan.CurrentMean
