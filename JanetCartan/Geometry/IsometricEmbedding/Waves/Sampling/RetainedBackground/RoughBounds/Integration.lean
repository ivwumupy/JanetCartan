module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.CompactJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Expectation.ScalarMass

/-!
# Physical seminorms under the original carrier integral

Dominated differentiation proves the real tensor estimates used in
`app:ch_waves:eq:background-quadrature-rough`. The density is the original
patch weight times a block or colored mask. No physical derivative of that
density is taken and no differentiation-under-integral hypothesis is assumed.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A smooth compact carrier density gives a smooth physical tensor integral
(`app:ch_waves:eq:background-quadrature-rough`). -/
theorem contDiff_weightedCarrierIntegral [CompleteSpace V]
    {w : Point → ℝ} (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    {H : Euclidean n × Point → V} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun x ↦ ∫ z, w z • H (x, z)) := by
  have he (x : Euclidean n) : (∫ z, w z • H (x, z)) =
      ∫ z in tsupport w, w z • H (x, z) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  simp_rw [he]
  let : IsFiniteMeasure (volume.restrict (tsupport w)) :=
    ⟨by simpa using hwc.measure_lt_top (μ := volume)⟩
  apply contDiffOn_univ.mp
  apply contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ hwc
    (subset_univ _) ((hw.comp contDiff_snd).smul hH).contDiffOn

/-- Original real carrier integration preserves the physical jet bounds,
with precisely the integral of its nonnegative density as the cost
(`app:ch_waves:eq:background-quadrature-rough`). -/
theorem cNorm_weightedCarrierIntegral_le
    {w : Point → ℝ} (hwi : Integrable w) (hwn : ∀ z, 0 ≤ w z)
    {H : Euclidean n × Point → V} (hH : ContDiff ℝ ∞ H)
    {A : ℕ → ℝ} {r : ℕ} (hA : ∀ j ≤ r, 0 ≤ A j)
    (hj : ∀ j ≤ r, ∀ z x,
      ‖iteratedFDeriv ℝ j (fun y ↦ H (y, z)) x‖ ≤ A j)
    (K : Set (Euclidean n)) :
    cNorm K r (fun x ↦ ∫ z, w z • H (x, z)) ≤
      (∫ z, w z) * ∑ j ∈ Finset.range (r + 1), A j := by
  have hs (z : Point) : ContDiff ℝ ∞ (fun x ↦ H (x, z)) :=
    hH.comp (contDiff_id.prodMk contDiff_const)
  have hm (j : ℕ) (x : Euclidean n) : Continuous
      (fun z ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, z)) x) := by
    have hh := RawPrimary.contDiffOn_atomPhysicalJet isOpen_univ isOpen_univ
      (show ContDiffOn ℝ ∞ H (univ ×ˢ univ) from hH.contDiffOn) j
    exact (contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hh)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have he (j : ℕ) (z : Point) (x : Euclidean n) :
      iteratedFDeriv ℝ j (fun y ↦ w z • H (y, z)) x =
        w z • iteratedFDeriv ℝ j (fun y ↦ H (y, z)) x :=
    iteratedFDeriv_const_smul_apply' ((hs z).of_le (by simp)).contDiffAt
  have hb (j : ℕ) (hjr : j ≤ r) : ∀ᵐ z, ∀ x ∈ (univ : Set (Euclidean n)),
      ‖iteratedFDeriv ℝ j (fun y ↦ w z • H (y, z)) x‖ ≤ w z * A j := by
    filter_upwards [] with z x _
    rw [he, norm_smul, Real.norm_of_nonneg (hwn z)]
    exact mul_le_mul_of_nonneg_left (hj j hjr z x) (hwn z)
  have hh := MeasureEnvelopes.cNorm_integral_le isOpen_univ
    (A := fun z x ↦ w z • H (x, z)) (b := fun j z ↦ w z * A j)
    (Eventually.of_forall fun z x _ ↦ ((hs z).of_le (by simp)).contDiffAt.const_smul (w z))
    (fun j _ x _ ↦ by
      simp_rw [he]
      exact hwi.aestronglyMeasurable.smul (hm j x).aestronglyMeasurable)
    (fun j _ ↦ hwi.mul_const (A j)) hb
    (fun j hjr ↦ Eventually.of_forall fun z ↦ mul_nonneg (hwn z) (hA j hjr))
    (subset_univ K)
  simpa only [integral_mul_const, Finset.mul_sum] using hh

end JanetCartan.Sampling.RetainedBackground
