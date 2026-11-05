module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BalancedNative
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.PeriodicComparison

/-!
# The common sampled row compared with the original native carrier family

Reassemble every balanced detector copy, identify each native weighted kernel
with its original continuum carrier, and apply the SAME event and colored
estimate. The resulting raw normal comparison supplies `CanonicalBandBounds`
with the original auxiliary normal and continuum inverse. No canonical normal
comparison is assumed and no sampled inverse is constructed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison
open ContinuumRow Sampling Sampling.Realization SamplingKernelBounds RawInputPartition
open RawCutoffBounds PeriodicLocalL2 AmplitudeBound SeparatedSampling

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I] {n N bands p : ℕ}
    (d : A → CarrierData n N)
    (ηb : A → I → Euclidean (n - 1)) (radius : A → I → ℝ)
    (hηb : ∀ a i, ηb a i ≠ 0) (hradius : ∀ a i, 0 < radius a i)
    (D₀ : A → BandKernelData (Fin bands × Point) n)
    (hfloor : ∀ a η, ‖η‖ ≤ 1 → (D₀ a).mask η = 0)
    (ψ : A → Point → ℝ) {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hc : ∀ a, Continuous (ψ a))
    (bump : A → I → Point → ℝ) (hbump : ∀ a i z, bump a i z ∈ Icc (0 : ℝ) 1)
    (hbc : ∀ a i, Continuous (bump a i))
    (hcover : ∀ a z, ψ a z ≠ 0 → ∀ η, (D₀ a).mask η ≠ 0 → ∃ i, bump a i z = 1 ∧
      NormedSpace.normalize η ∈ Metric.ball (NormedSpace.normalize (ηb a i))
        (CanonicalConic.angularWidth (ηb a i) (radius a i) / 4))
    (hDzero : ∀ a (j : Fin bands) z η, η ∉ wideBand n j.val →
      ∀ x, (D₀ a).kernel (j, z) η x = 0)
    (hkernel : ∀ a (j : Fin bands) x u,
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) • carrierKernel (d a) x u =
        Real.sqrt (ψ a (carrierSamplingEquiv u.1)) •
          (D₀ a).kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x))
    (hhigh : ∀ a t, t ≤ 1 → (d a).highCutoff t = 0)
    (U : A → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ a q, (U a).adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral (d a) q)

include hψ hc hbump hbc hcover hDzero hkernel hhigh hU

/-- The finite family of native balanced prefixes is the original continuum
raw square. `hkernel` is the literal identity proved by
`nativeTransportKernel_eq_weighted_original` for the actual retained constructor;
no norm comparison is among these inputs
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_mean_pairs:defn:mean-canonical`). -/
theorem family_balancedNativePrefix_normal_eq_original
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands) :
    transferOperator ((4 : ℝ) • realOutputCompression
      (∑ c : A × ((s : Finset I) × s), ∫ z : Point,
        balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1 z • atomNormal
          (Real.sqrt c.2.1.card • refinedKernelPrefix
            (jointSubsetKernel (ηb c.1) (radius c.1) (hηb c.1) (hradius c.1)
              (D₀ c.1) (hfloor c.1) c.2.1 c.2.2) (cutoffCount cutoff) z))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
        ∑ a, (carrierChannel (U a)).comp
          ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
            (carrierChannel (U a)).adjoint) := by
  classical
  have hsum (f : A → Output n →L[ℂ] Output n) :
      transferOperator ((4 : ℝ) • realOutputCompression (∑ a, f a)) =
        ∑ a, transferOperator ((4 : ℝ) • realOutputCompression (f a)) := by
    ext1 q
    simp [transferOperator, realOutputCompression, Finset.smul_sum]
  rw [Fintype.sum_prod_type, hsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact balanced_nativeSamplingPrefix_normal_eq_original (ηb a) (radius a) (hηb a) (hradius a)
    (D₀ a) (hfloor a) (ψ a) (hψ a) (hc a) (bump a) (hbump a) (hbc a) (hcover a)
    (d a) (hDzero a) (hkernel a) (hhigh a) (U a) (hU a) cutoff hL

variable (w : ℝ → ℝ) {W h : ℝ} (hw : WindowBounds p w W) (hh : 0 ≤ h)
    (ξ : A × ((s : Finset I) × s) → ShiftSpace p B h)
    (D : A × ((s : Finset I) × s) →
      BandKernelData (Fin bands × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (auxiliary : OutputL2 n →L[ℝ] OutputL2 n)
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ bands)
    {samplingError transportError : ℝ}
    (hevent : ‖familyDeviation p B
      (fun c : A × ((s : Finset I) × s) ↦
        balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1) w h
      (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z)) ξ‖ ≤
        samplingError)
    (htransport : ‖(∑ c : A × ((s : Finset I) × s),
      patchMeanNormal p B (balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1) w h
        (fun color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z))) -
      (∑ c : A × ((s : Finset I) × s), ∫ z : Point,
        balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1 z • atomNormal
          (Real.sqrt c.2.1.card • refinedKernelPrefix
            (jointSubsetKernel (ηb c.1) (radius c.1) (hηb c.1) (hradius c.1)
              (D₀ c.1) (hfloor c.1) c.2.1 c.2.2) (cutoffCount cutoff) z))‖ ≤ transportError)

include hw hh hevent htransport hL hηb hradius hfloor

/-- The SAME common sample compares the finite corrected raw-integral row
with the original continuum raw square after reassembling all native copies.
The event and colored estimates refer to the final supplied kernels `D`, and
the reference is identified above from literal kernels and raw adjoints.
This is the comparison consumed by `CanonicalChange.Comparison` and
`CanonicalBandBounds`, with the unchanged auxiliary normal
(`app:ch_mean_pairs:eq:mean-normal-comparison`, `main:prop:canonical`). -/
theorem balancedNative_rawIntegral_normal_sub_original_le :
    let weights := fun c : A × ((s : Finset I) × s) ↦
      balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1
    let row := CanonicalRow.weightedRow
      (sampleWeight (p := p) B weights w h (fun c ↦ extendedShift (ξ c)))
      (rawIntegralSampledComponent B weights w h (fun c ↦ extendedShift (ξ c))
        (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z)))
    ‖(auxiliary + row.comp row.adjoint) -
      (auxiliary + ∑ a, (carrierChannel (U a)).comp
        ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
          (carrierChannel (U a)).adjoint))‖ ≤
      (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 * (4 * (samplingError + transportError)) := by
  let weights := fun c : A × ((s : Finset I) × s) ↦
    balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1
  have hμ := sampleWeight_nonneg (P := fun c : A × ((s : Finset I) × s) ↦ P c.1)
    (fun c ↦ extendedShift (ξ c)) hw
    (fun c ↦ balancedCarrierSubsetWeight_patchBounds (ψ c.1) (bump c.1)
      (hψ c.1) (hbump c.1) c.2.1) hh
  have he := rawIntegral_sampled_normal_sub_transport_le B weights w h ξ
    (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z))
    (fun c z ↦ Real.sqrt c.2.1.card • refinedKernelPrefix
      (jointSubsetKernel (ηb c.1) (radius c.1) (hηb c.1) (hradius c.1)
        (D₀ c.1) (hfloor c.1) c.2.1 c.2.2) (cutoffCount cutoff) z)
    hμ auxiliary hevent htransport
  dsimp only [weights] at he
  rw [family_balancedNativePrefix_normal_eq_original d ηb radius hηb hradius D₀ hfloor
    ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU cutoff hL] at he
  have hnz : (2 * Real.pi) ^ (-(n : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity : 0 < 2 * Real.pi) _).ne'
  have hcancel : (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 *
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hnz, one_pow]
  rw [smul_smul, hcancel, one_smul] at he
  exact he

/-- Apply the derived normal comparison to the ORIGINAL continuum inverse.
The unweighted raw adjoints precede that inverse and no inverse sample weight
appears. This instantiates the canonical weighted-energy consumer for the
identified finite native family (`app:ch_mean_pairs:eq:mean-canonical-weighted-low`). -/
theorem balancedNative_sum_weighted_adjoint_inverse_norm_sq_le
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) {M L : ℝ}
    (hauxiliary : ∀ q, 0 ≤ inner ℝ (auxiliary q) q)
    (hreference : ‖auxiliary + ∑ a, (carrierChannel (U a)).comp
      ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
        (carrierChannel (U a)).adjoint)‖ ≤ M)
    (hQ₀ : ‖Q₀‖ ≤ L) (r : OutputL2 n) :
    let weights := fun c : A × ((s : Finset I) × s) ↦
      balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1
    let μ := sampleWeight (p := p) B weights w h (fun c ↦ extendedShift (ξ c))
    let Araw := rawIntegralSampledComponent B weights w h (fun c ↦ extendedShift (ξ c))
      (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z))
    ∑ i, μ i * ‖(Araw i).adjoint (Q₀ r)‖ ^ 2 ≤
      (M + (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 *
        (4 * (samplingError + transportError))) * L ^ 2 * ‖r‖ ^ 2 := by
  let weights := fun c : A × ((s : Finset I) × s) ↦
    balancedCarrierSubsetWeight (ψ c.1) (bump c.1) c.2.1
  let μ := sampleWeight (p := p) B weights w h (fun c ↦ extendedShift (ξ c))
  let Araw := rawIntegralSampledComponent B weights w h (fun c ↦ extendedShift (ξ c))
    (fun c color z ↦ refinedKernelPrefix (D c) (cutoffCount cutoff) (color, z))
  have hμ := sampleWeight_nonneg (P := fun c : A × ((s : Finset I) × s) ↦ P c.1)
    (fun c ↦ extendedShift (ξ c)) hw
    (fun c ↦ balancedCarrierSubsetWeight_patchBounds (ψ c.1) (bump c.1)
      (hψ c.1) (hbump c.1) c.2.1) hh
  exact CanonicalBandBounds.sum_weighted_adjoint_inverse_norm_sq_le μ hμ Araw
    (auxiliary + (CanonicalRow.weightedRow μ Araw).comp (CanonicalRow.weightedRow μ Araw).adjoint)
    auxiliary (auxiliary + ∑ a, (carrierChannel (U a)).comp
      ((carrierSquaredCutoff (roundedCarrierMask n cutoff)).comp
        (carrierChannel (U a)).adjoint)) Q₀ rfl hauxiliary hreference
    (balancedNative_rawIntegral_normal_sub_original_le d ηb radius hηb hradius D₀ hfloor
      ψ hψ hc bump hbump hbc hcover hDzero hkernel hhigh U hU w hw hh ξ D auxiliary
      cutoff hL hevent htransport) hQ₀ r

end JanetCartan.CanonicalRowComparison
