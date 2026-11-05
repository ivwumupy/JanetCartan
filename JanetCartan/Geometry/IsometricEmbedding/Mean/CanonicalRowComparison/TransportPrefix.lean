module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.OutputCompatibility
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.CarrierIntegral

/-!
# Every grouped transport prefix has its literal continuum normal

Reassemble the constructed bands using the original prefix labels. The
bandwidth, carrier weight, smooth masks, Fourier scalar and raw measures
remain unchanged. The real normal is exactly the endpoint appearing in
`refined_complete_normal_sub_transport_le`, including factor four.

This is identification of the supplied transport family. Comparing its
prepared scalar with the original positive scalar, and assembling the
original weighted detector partition, remain separate producer obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow CurrentMean Sampling Sampling.RawKernel Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition PeriodicLocalL2 AmplitudeBound SeparatedSampling

variable {n N bands : ℕ}
    (d : CarrierData n N)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (Yext : Point × Euclidean n → Euclidean (n - 1))
    (hY : Continuous Yext)
    (hA : Continuous (fun q : (Point × Euclidean n) × Euclidean (n - 1) ↦
      transportCrossBandAmplitude d C q.1.1 q.1.2 q.2))
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (hsupport : ∀ z x η, x ∉ K → transportCrossBandAmplitude d C z x η = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z x η, ‖transportCrossBandAmplitude d C z x η‖ ≤ M)
    (hpoint : ∀ x, d.chartPoint x = centeredTorusRepresentative x)
    (hC : ∀ x, C (centeredTorusRepresentative x) = preparationMeasurement d x)
    (hphase : ∀ x z η, transportCrossBandAmplitude d C (carrierSamplingEquiv z)
      (centeredTorusRepresentative x) η ≠ 0 →
      inner ℝ (Yext (carrierSamplingEquiv z, centeredTorusRepresentative x)) η =
        carrierPhase d x (z, η))
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)

local notation "D₀" => transportCrossBandKernelData (bands := bands) d C Yext hY hA K hK hsupport M hM hbound
local notation "T" => transportBandContinuumOperator (bands := bands) d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase

/-- The SAME continuum band operators form each literal grouped prefix.
The input of each band remains the original carrier Lebesgue L² space
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def transportContinuumPrefix (L : ℕ) :
    PiLp 2 (fun _ : Fin bands ↦ CarrierL2 n) →L[ℂ] ComplexOutputL2 n :=
  NormalPerturbation.weightedRow (fun j : Fin bands ↦ if j.val < L then 1 else 0)
    (fun j ↦ T j ψ hψ hc)

/-- Exact normal identification for EVERY prefix of the fixed ceiling.
The proof uses constructed forward kernels, original wide-band reassembly,
and the original sampling measure. It assumes no equality of normal operators
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem transportContinuumPrefix_normal (L : ℕ) :
    let A := transportContinuumPrefix (bands := bands) d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase ψ hψ hc L
    A.comp A.adjoint = transferOperator
      (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D₀ L z)) := by
  classical
  dsimp only
  have hnormal : (transportContinuumPrefix (bands := bands)
        d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc L).comp
      (transportContinuumPrefix (bands := bands)
        d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc L).adjoint =
      ∑ j ∈ Finset.univ.filter (fun j : Fin bands ↦ j.val < L), atomNormal (T j ψ hψ hc) := by
    have hw (j : Fin bands) : 0 ≤ (if j.val < L then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    simpa only [transportContinuumPrefix, Finset.sum_filter, NormalPerturbation.normal,
      atomNormal, apply_ite, RCLike.ofReal_one, RCLike.ofReal_zero,
      ite_smul, one_smul, zero_smul] using
        NormalPerturbation.normal_weightedRow (𝕜 := ℂ)
          (fun j : Fin bands ↦ if j.val < L then 1 else 0) hw (fun j ↦ T j ψ hψ hc)
  rw [hnormal]
  have hi (j : Fin bands) : Integrable (fun z : Point ↦
      ψ z • atomNormal (wideBandKernelOperator D₀ j.val (j, z))) := by
    simpa only [id_eq] using integrable_wideBand_patch_normal D₀ j id continuous_id hψ hc
  have hband (j : Fin bands) :
      atomNormal (T j ψ hψ hc) =
        transferOperator (∫ z : Point, ψ z • atomNormal (wideBandKernelOperator D₀ j.val (j, z))) := by
    change (T j ψ hψ hc).comp (T j ψ hψ hc).adjoint = _
    rw [transportBandContinuumOperator_normal, transferOperator_sampling_integral _ (hi j)]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [transferOperator, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp_rw [hband]
  have hsum (s : Finset (Fin bands))
      (a : Fin bands → Output n →L[ℂ] Output n) :
      (∑ j ∈ s, transferOperator (a j)) = transferOperator (∑ j ∈ s, a j) := by
    ext1 v
    simp [transferOperator]
  rw [hsum, ← integral_finsetSum _ (fun j _ ↦ hi j)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ColoredNormalComparison.refinedKernelPrefix_normal_eq_wide, Finset.smul_sum]
  rfl

/-- The real transport prefix is exactly the sampling comparison's output
endpoint, with both complex input quadratures and the factor FOUR forced by
the factor TWO cross response (`app:ch_waves:eq:real-normal`,
`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem real_transportContinuumPrefix_normal (L : ℕ) :
    let A := realQuadratureChannel (transportContinuumPrefix (bands := bands)
      d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc L)
    A.comp A.adjoint = transferOperator ((4 : ℝ) • realOutputCompression
      (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D₀ L z))) := by
  dsimp only
  rw [realQuadratureChannel_normal_eq_four_realPart,
    transportContinuumPrefix_normal, realOutputCompression_transferOperator]
  simp only [transferOperator, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end JanetCartan.CanonicalRowComparison
