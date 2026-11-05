module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSample
public import JanetCartan.Iteration.PhysicalBackground.NativePositiveCancellation
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open ContinuumRow PositiveBackground NormalizedBackground UniformStep.Periodization

/-- The original affine density mean is smooth on its retained physical
carrier neighborhood. Only smoothness of the actual density is needed, not
its positivity or a bound on the mean (`app:ch_background:eq:bg-affine-mean`). -/
theorem affine_density_mean_smooth {n N : ℕ} {I : Type*} [Fintype I]
    (d : I → CarrierData n N) (χ : I → CarrierParameter → ℝ)
    (hχ : ∀ a, ContDiff ℝ ∞ (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    {W : Set (Euclidean n)} (hW : IsOpen W) (V : I → Set CarrierParameter)
    (hV : ∀ a, IsOpen (V a)) (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hY : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).transportedPosition p.1 p.2) (W ×ˢ V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).normalField p.1 p.2) (W ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).covector p.1 p.2) (W ×ˢ V a))
    (v : I → CarrierVariable n → ℝ) (hv : ∀ a, ContDiff ℝ ∞ (v a)) :
    ContDiffOn ℝ ∞ (physicalDensityMean d χ v) W := by
  let (a : I) : IsFiniteMeasure ((volume.prod volume).restrict (tsupport (χ a))) :=
    ⟨by simpa using (hχc a).measure_lt_top (μ := volume.prod volume)⟩
  unfold physicalDensityMean
  apply ContDiffOn.sum
  intro a _
  let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n := ⟨L,L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have he : (fun x ↦ ∫ z, (χ a z ^ 2 * (1 + v a (z, (d a).transportedPosition x z))) *
      ‖(d a).normalField x z‖ ^ 2 * ((d a).covector x z i * (d a).covector x z j) ∂(volume.prod volume)) =
      fun x ↦ ∫ z in tsupport (χ a), (χ a z ^ 2 * (1 + v a (z, (d a).transportedPosition x z))) *
      ‖(d a).normalField x z‖ ^ 2 * ((d a).covector x z i * (d a).covector x z j) ∂(volume.prod volume) := by
    funext x
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp only [image_eq_zero_of_notMem_tsupport hz,zero_pow (by decide : 2 ≠ 0),zero_mul]
  rw [he]
  have hb := SourceGeometry.contDiffOn_carrierMean_integrand ((hχ a).pow 2 |>.contDiffOn) (hν a) (hξ a) i j
  have hd : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ 1 + v a (p.2,(d a).transportedPosition p.1 p.2)) (W ×ˢ V a) :=
    contDiffOn_const.add ((hv a).comp_contDiffOn (contDiffOn_snd.prodMk (hY a)))
  have ht : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (χ a p.2 ^ 2 * (1 + v a (p.2, (d a).transportedPosition p.1 p.2))) *
      ‖(d a).normalField p.1 p.2‖ ^ 2 * ((d a).covector p.1 p.2 i * (d a).covector p.1 p.2 j)) (W ×ˢ V a) := by
    convert hb.mul hd using 1
    funext p
    ring
  exact contDiffOn_compactParameterIntegral (μ := volume.prod volume) hW (hV a) (hχc a) (hχV a) ht

/-- The existing physical measurement localizes the affine mean. Its actual
support is already strictly inside the original smoothness region. -/
theorem measured_local_tensor_smooth {n : ℕ}
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    {W : Set (Euclidean n)} (hW : IsOpen W) (hs : tsupport C ⊆ W)
    (H : MetricField n) (hH : ContDiffOn ℝ ∞ H W) :
    ContDiff ℝ ∞ (fun x ↦ C x (H x)) ∧ tsupport (fun x ↦ C x (H x)) ⊆ tsupport C := by
  have ht : tsupport (fun x ↦ C x (H x)) ⊆ tsupport C := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    apply subset_tsupport C
    intro he
    exact hx (by simp only [he,zero_apply])
  exact ⟨Localization.contDiff_of_contDiffOn_support_neighborhood hW (hC.contDiffOn.clm_apply hH) (ht.trans hs),ht⟩

theorem physical_measurement_inner {n : ℕ} (Q : Euclidean n → Fin n → MetricTensor n)
    {r : ℝ} (hr : 0 < r) : tsupport (Sampling.canonicalSamplingMeasurement Q hr) ⊆ ball 0 (4*r) := by
  apply (Sampling.tsupport_canonicalSamplingMeasurement Q hr).trans
  apply (FixedCutoffs.physical_tsupport hr 1).trans
  apply ball_subset_ball
  norm_num
  linarith

/-- Smooth measured affine leading mean, with exactly the same physical
measurement and centered representative. No new cutoff enters the value. -/
def measuredLeadingResidual {n : ℕ}
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    {W : Set (Euclidean n)} (hW : IsOpen W) (hs : tsupport C ⊆ W)
    {b : ℝ} (hb : b < 1/2) (hbox : tsupport C ⊆ {x | ∀ i, |x i| ≤ b})
    (H : MetricField n) (hH : ContDiffOn ℝ ∞ H W) : CurrentMean.SmoothResidual n :=
  ⟨fun z _ ↦ C (AmplitudeBound.centeredTorusRepresentative z) (H (AmplitudeBound.centeredTorusRepresentative z)),
    fun _ ↦ isSmoothPeriodic_vectorPeriodization hb ((measured_local_tensor_smooth C hC hW hs H hH).2.trans hbox)
      (measured_local_tensor_smooth C hC hW hs H hH).1⟩

/-- The actual native measurement buffer gives the measured affine leading
field, without a new extension or cutoff (`new:eq:mean-source`). -/
def nativeAffineLeading {n N : ℕ} {I : Type*} [Fintype I]
    (d : I → CarrierData n N) (χ : I → CarrierParameter → ℝ)
    (hχ : ∀ a, ContDiff ℝ ∞ (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    {r : ℝ} (hr : 0 < r) (hcell : 4*r < 1/2)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (hC : ContDiff ℝ ∞ (Sampling.canonicalSamplingMeasurement Q hr))
    (V : I → Set CarrierParameter) (hV : ∀ a, IsOpen (V a)) (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hY : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).transportedPosition p.1 p.2) (ball 0 (4*r) ×ˢ V a))
    (hν : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).normalField p.1 p.2) (ball 0 (4*r) ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).covector p.1 p.2) (ball 0 (4*r) ×ˢ V a))
    (v : I → CarrierVariable n → ℝ) (hv : ∀ a, ContDiff ℝ ∞ (v a)) : CurrentMean.SmoothResidual n :=
  measuredLeadingResidual (Sampling.canonicalSamplingMeasurement Q hr) hC isOpen_ball
    (physical_measurement_inner Q hr) hcell (by
      intro x hx i
      exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp
        (FixedCutoffs.physical_tsupport_four hr 1 (Sampling.tsupport_canonicalSamplingMeasurement Q hr hx))))
    (physicalDensityMean d χ v) (affine_density_mean_smooth d χ hχ hχc isOpen_ball V hV hχV hY hν hξ v hv)

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end
