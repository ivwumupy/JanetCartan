module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.NativeBand

/-!
# Reassemble native transport bands on the original raw cutoff

Every grouped prefix retains both sharp annular pieces. Their native weighted
kernels identify the same continuum carrier and rounded raw square. Consumer:
`app:ch_mean_pairs:eq:mean-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CanonicalRowComparison
open ContinuumRow Sampling Sampling.MeanNormalBound SamplingKernelBounds RawInputPartition
open RawCutoffBounds CanonicalTailRealization PeriodicLocalL2 AmplitudeBound SeparatedSampling
variable {n N bands : ℕ}

/-- Every native grouped transport prefix has the original rounded raw normal.
The literal weighted kernel is identified separately by the actual transport
constructor; the normal and all integral exchanges are derived here
(`app:ch_waves:eq:sampling-prefix-normal`, `main:eq:linear-two-errors`). -/
theorem nativeSamplingPrefix_normal_eq_original
    (d : CarrierData n N) (D : BandKernelData (Fin bands × Point) n)
    (hDzero : ∀ j : Fin bands, ∀ z η, η ∉ wideBand n j.val →
      ∀ x, D.kernel (j, z) η x = 0)
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (hkernel : ∀ j : Fin bands, ∀ x u,
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) • carrierKernel d x u =
        Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
          D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x))
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    transferOperator ((4 : ℝ) • realOutputCompression
      (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D (cutoffCount cutoff) z))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
        (carrierChannel U).comp ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
          (carrierChannel U).adjoint) := by
  classical
  let s := Finset.univ.filter (fun j : Fin bands ↦ j.val < cutoffCount cutoff)
  have hi (j : Fin bands) : Integrable (fun z : Point ↦
      ψ z • atomNormal (wideBandKernelOperator D j.val (j, z))) :=
    integrable_wideBand_patch_normal D j id continuous_id hψ hc
  have he : (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D (cutoffCount cutoff) z)) =
      ∑ j ∈ s, ∫ z : Point, ψ z • atomNormal (wideBandKernelOperator D j.val (j, z)) := by
    rw [← integral_finsetSum _ (fun j _ ↦ hi j)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [ColoredNormalComparison.refinedKernelPrefix_normal_eq_wide, Finset.smul_sum]
    rfl
  rw [he]
  have hsum (a : Fin bands → Output n →L[ℂ] Output n) :
      transferOperator ((4 : ℝ) • realOutputCompression (∑ j ∈ s, a j)) =
        ∑ j ∈ s, transferOperator ((4 : ℝ) • realOutputCompression (a j)) := by
    ext1 q
    simp [transferOperator, realOutputCompression, Finset.smul_sum]
  rw [hsum]
  simp_rw [nativeSamplingBand_normal_eq_original d D _ (hDzero _) ψ hψ hc
    (hkernel _) U hU]
  rw [← Finset.smul_sum, originalCarrier_band_normals_eq_rounded d hhigh U hU cutoff hL]

end JanetCartan.CanonicalRowComparison
