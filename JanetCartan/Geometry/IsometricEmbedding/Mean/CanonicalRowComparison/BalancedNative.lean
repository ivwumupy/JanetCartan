module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.NativePrefix
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BalancedNormal

/-!
# Reassemble the native balanced detector copies

Integrate the sampling producer's exact balanced-copy identity on its original
carrier measure. The native high-pass stays in the mask, and the label-count
factor stays on the channel. The copied weights preserve the uncut zero-atom
background. Their prefix normals reassemble before identifying the original
continuum raw square; no copied-weight plateau is imposed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow Sampling Sampling.MeanNormalBound SamplingKernelBounds RawInputPartition
open RawCutoffBounds PeriodicLocalL2 AmplitudeBound SeparatedSampling

variable {n N bands : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ a, ηb a ≠ 0) (hr : ∀ a, 0 < r a)
    (D : BandKernelData (Fin bands × Point) n)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (b : I → Point → ℝ) (hb : ∀ a z, b a z ∈ Icc (0 : ℝ) 1)
    (hbc : ∀ a, Continuous (b a))
    (hcover : ∀ z, ψ z ≠ 0 → ∀ η, D.mask η ≠ 0 → ∃ a, b a z = 1 ∧
      NormedSpace.normalize η ∈ Metric.ball (NormedSpace.normalize (ηb a))
        (CanonicalConic.angularWidth (ηb a) (r a) / 4))

include hψ hc hb hbc hcover

/-- The SAME balanced carrier weights and normalized angular copies have the
parent integral normal. Compact patch bounds prove every Bochner exchange;
there is no division by a sample weight (`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_waves:eq:background-quadrature`). -/
theorem integral_balancedNativePrefix_normal (L : ℕ) :
    (∑ c : (s : Finset I) × s, ∫ z : Point,
      balancedCarrierSubsetWeight ψ b c.1 z • atomNormal
        (Real.sqrt c.1.card • refinedKernelPrefix
          (jointSubsetKernel ηb r hηb hr D hfloor c.1 c.2) L z)) =
      ∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D L z) := by
  classical
  have hi (c : (s : Finset I) × s) : Integrable (fun z : Point ↦
      balancedCarrierSubsetWeight ψ b c.1 z • atomNormal
        (Real.sqrt c.1.card • refinedKernelPrefix
          (jointSubsetKernel ηb r hηb hr D hfloor c.1 c.2) L z)) :=
    integrable_patch_normal (balancedCarrierSubsetWeight_patchBounds ψ b hψ hb c.1)
      (continuous_balancedCarrierSubsetWeight ψ b hc hbc c.1) _
      ((continuous_refinedKernelPrefix
        (jointSubsetKernel ηb r hηb hr D hfloor c.1 c.2) L).const_smul (Real.sqrt c.1.card))
  rw [← integral_finsetSum _ (fun c _ ↦ hi c)]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [Fintype.sum_sigma] using
    sum_balancedCarrierSubsetWeight_jointSubsetKernel_prefix_normal
      ηb r hηb hr D hfloor ψ b z (hcover z) L z

/-- Reassembled native detector copies give the SAME original rounded raw
normal, with the unchanged Fourier scalar and factor-four real compression.
The supplied literal kernel is consumed before any inverse is used
(`app:ch_mean_pairs:eq:mean-normal-comparison`, `main:prop:canonical`). -/
theorem balanced_nativeSamplingPrefix_normal_eq_original
    (d : CarrierData n N)
    (hDzero : ∀ j : Fin bands, ∀ z η, η ∉ wideBand n j.val →
      ∀ x, D.kernel (j, z) η x = 0)
    (hkernel : ∀ j : Fin bands, ∀ x u,
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) • carrierKernel d x u =
        Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
          D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x))
    (hhigh : ∀ t, t ≤ 1 → d.highCutoff t = 0)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q)
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    transferOperator ((4 : ℝ) • realOutputCompression
      (∑ c : (s : Finset I) × s, ∫ z : Point,
        balancedCarrierSubsetWeight ψ b c.1 z • atomNormal
          (Real.sqrt c.1.card • refinedKernelPrefix
            (jointSubsetKernel ηb r hηb hr D hfloor c.1 c.2) (cutoffCount cutoff) z))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
        (carrierChannel U).comp ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
          (carrierChannel U).adjoint) := by
  rw [integral_balancedNativePrefix_normal ηb r hηb hr D hfloor ψ hψ hc b hb hbc hcover]
  exact nativeSamplingPrefix_normal_eq_original d D hDzero ψ hψ hc hkernel
    hhigh U hU cutoff hL

end JanetCartan.CanonicalRowComparison
