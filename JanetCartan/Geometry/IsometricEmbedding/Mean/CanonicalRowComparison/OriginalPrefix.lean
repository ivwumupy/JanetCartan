module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.OriginalBand
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.OriginalCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportPrefix

/-!
# The transport prefix is the original continuum raw square

The unchanged band masks, external-weight plateau, literal continuum
adjoint and floor-one high cutoff identify the sampling comparison's
transport endpoint with the original carrier at the rounded raw cutoff.
All Fourier and polarization factors remain visible. This is identification
on the supplied carrier data; changing the prepared scalar still requires
its full two-position amplitude estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow RawInputPartition RawCutoffBounds CanonicalTailRealization
open Sampling SamplingKernelBounds SeparatedSampling PeriodicLocalL2 AmplitudeBound

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
    (hC : ∀ x, C (centeredTorusRepresentative x) = CurrentMean.preparationMeasurement d x)
    (hphase : ∀ x z η, transportCrossBandAmplitude d C (carrierSamplingEquiv z)
      (centeredTorusRepresentative x) η ≠ 0 →
      inner ℝ (Yext (carrierSamplingEquiv z, centeredTorusRepresentative x)) η =
        carrierPhase d x (z, η))
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (hψone : ∀ z η, d.angularCutoff z η ≠ 0 → ψ (carrierSamplingEquiv z) = 1)
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)

local notation "T" => transportBandContinuumOperator (bands := bands) d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase
local notation "D₀" => transportCrossBandKernelData (bands := bands) d C Yext hY hA K hK hsupport M hM hbound

include hψone hhigh hU

/-- Every retained transport prefix is the raw rounded square on the SAME
original carrier and its original adjoint. The external plateau and high-pass
are the original geometric producer inputs; the normal identity is derived.
The displayed Fourier scalar is squared, in addition to the factor four
already contained in `carrierChannel` (`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_mean_pairs:eq:mean-normal-comparison`). -/
theorem real_transportContinuumPrefix_normal_eq_original
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    let A := realQuadratureChannel (transportContinuumPrefix (bands := bands)
      d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase ψ hψ hc (cutoffCount cutoff))
    A.comp A.adjoint = ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
      (carrierChannel U).comp ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
        (carrierChannel U).adjoint) := by
  classical
  dsimp only
  let s := Finset.univ.filter (fun j : Fin bands ↦ j.val < cutoffCount cutoff)
  have hnormal :
      (transportContinuumPrefix (bands := bands) d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase ψ hψ hc (cutoffCount cutoff)).comp
      (transportContinuumPrefix (bands := bands) d C Yext hY hA K hK hsupport M hM hbound
        hpoint hC hphase ψ hψ hc (cutoffCount cutoff)).adjoint =
      ∑ j ∈ s, (T j ψ hψ hc).comp (T j ψ hψ hc).adjoint := by
    have hw (j : Fin bands) : 0 ≤ (if j.val < cutoffCount cutoff then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    simpa only [transportContinuumPrefix, Finset.sum_filter, NormalPerturbation.normal,
      apply_ite, RCLike.ofReal_one, RCLike.ofReal_zero, ite_smul, one_smul, zero_smul, s] using
        NormalPerturbation.normal_weightedRow (𝕜 := ℂ)
          (fun j : Fin bands ↦ if j.val < cutoffCount cutoff then 1 else 0) hw
          (fun j ↦ T j ψ hψ hc)
  rw [realQuadratureChannel_normal_eq_four_realPart, hnormal]
  have hsum : (4 : ℝ) • realOutputCompression
      (∑ j ∈ s, (T j ψ hψ hc).comp (T j ψ hψ hc).adjoint) =
      ∑ j ∈ s, (realQuadratureChannel (T j ψ hψ hc)).comp
        (realQuadratureChannel (T j ψ hψ hc)).adjoint := by
    simp_rw [realQuadratureChannel_normal_eq_four_realPart]
    ext1 q
    simp [realOutputCompression, Finset.smul_sum]
  rw [hsum]
  simp_rw [real_transportBandContinuumOperator_eq_original d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc hψone U hU,
    map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
    ← pow_two]
  rw [← Finset.smul_sum, originalCarrier_band_normals_eq_rounded d hhigh U hU cutoff hL]

include hpoint hC hphase hψ hc in
/-- The transported uncolored endpoint of the actual sampling estimate is
the original carrier's rounded raw normal, with precisely its forced Fourier
scalar. This closes the operator-identification step, rather than assuming
equality of independently constructed normals
(`app:ch_waves:eq:colored-normal-comparison`, `main:eq:linear-two-errors`). -/
theorem transport_sampling_normal_eq_original
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    transferOperator ((4 : ℝ) • realOutputCompression
      (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D₀ (cutoffCount cutoff) z))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
        (carrierChannel U).comp ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
          (carrierChannel U).adjoint) := by
  rw [← real_transportContinuumPrefix_normal d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc]
  exact real_transportContinuumPrefix_normal_eq_original d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase ψ hψ hc hψone hhigh U hU cutoff hL

end JanetCartan.CanonicalRowComparison
