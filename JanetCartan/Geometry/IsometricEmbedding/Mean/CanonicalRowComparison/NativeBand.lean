module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.OriginalCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportPrefix

/-!
# Native sampling bands and the original carrier normal

The sampling producer retains its detector in the original frequency mask.
Identify its weighted kernel directly with the carrier kernel, construct its
bounded band operator, and derive the slice adjoints and normal disintegration.
This supplies the native endpoint for `app:ch_waves:eq:colored-normal-comparison`
without moving the detector into a different kernel's amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.CanonicalRowComparison
open ContinuumRow Sampling Sampling.MeanNormalBound SamplingKernelBounds RawInputPartition
open RawCutoffBounds CanonicalTailRealization PeriodicLocalL2 AmplitudeBound SeparatedSampling
variable {n N bands : ℕ}

/-- The native sampling band has the original carrier normal when its weighted
literal kernel agrees with the original smooth-band kernel. Compact bounds,
slice adjoints and disintegration are derived; no normal equality is a premise
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_background:eq:bg-T`). -/
theorem nativeSamplingBand_normal_eq_original
    (d : CarrierData n N) (D : BandKernelData (Fin bands × Point) n)
    (j : Fin bands)
    (hDzero : ∀ z η, η ∉ wideBand n j.val → ∀ x, D.kernel (j, z) η x = 0)
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (hkernel : ∀ x u,
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u) • carrierKernel d x u =
        Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
          D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ q, U.adjoint q =ᵐ[carrierMeasure n] carrierAdjointIntegral d q) :
    transferOperator ((4 : ℝ) • realOutputCompression
      (∫ z : Point, ψ z • atomNormal (wideBandKernelOperator D j.val (j, z)))) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2)) ^ 2 •
        ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val))).comp
          ((carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val))).adjoint := by
  let c : ℝ := (2 * Real.pi) ^ (-(n : ℝ) / 2)
  let m : CarrierVariable n → ℝ := fun u ↦ c * carrierBand n j.val u
  have heq (x) (u) : maskedCarrierKernel d m x u =
      Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
        D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x) := by
    simpa only [maskedCarrierKernel, m, c, Complex.coe_smul] using hkernel x u
  let H := weightedSamplingBandFiniteKernelBounds d m D j hDzero ψ hψ hc heq
  let T : CarrierL2 n →L[ℂ] ComplexOutputL2 n := CarrierRegularization.boundedKernelOperator
    (K := maskedCarrierKernel d m) H.stronglyMeasurable H.isCompact_initialSupport.measurableSet
    H.isCompact_initialSupport.measure_lt_top.ne H.kernel_eq_zero_off_initialSupport H.norm_le
  have hT (f : CarrierL2 n) : T f =ᵐ[volume] regularizedCarrierIntegral d m f := by
    filter_upwards [CarrierRegularization.boundedKernelOperator_ae
      (K := maskedCarrierKernel d m) H.stronglyMeasurable H.isCompact_initialSupport.measurableSet
      H.isCompact_initialSupport.measure_lt_top.ne H.kernel_eq_zero_off_initialSupport H.norm_le f]
      with x hx
    exact hx.trans (regularizedCarrierIntegral_eq_masked d m f x).symm
  let A := fun z : CarrierParameter ↦ (Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ) •
    transferOutputOperator (wideBandKernelOperator D j.val (j, carrierSamplingEquiv z))
  have hA (z : CarrierParameter) (f : WideBandL2 n j.val) :
      A z f =ᵐ[volume] regularizedCarrierSliceIntegral d m z f := by
    have hf := wideBandKernelOperator_ae_integral D j.val (j, carrierSamplingEquiv z)
      (hDzero (carrierSamplingEquiv z)) f
    filter_upwards [toTorus_coe (𝕜 := ℂ) (wideBandKernelOperator D j.val (j, carrierSamplingEquiv z) f),
      measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp hf.restrict,
      Lp.coeFn_smul (Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ)
        (toTorus (𝕜 := ℂ) (wideBandKernelOperator D j.val (j, carrierSamplingEquiv z) f))]
      with x hx hf hs
    change ((Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ) •
      toTorus (𝕜 := ℂ) (wideBandKernelOperator D j.val (j, carrierSamplingEquiv z) f)) x = _
    rw [hs, Pi.smul_apply, hx, hf]
    simp only [Function.comp_apply, regularizedCarrierSliceIntegral]
    conv_rhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := wideBand n j.val) (fun η hη ↦ by
      simp [maskedCarrierKernel, m, carrierBand, radialBand_eq_zero_off_wideBand hη])]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with η
    rw [heq]
    simp only [Complex.coe_smul]
    exact smul_comm _ _ _
  let S := fun z ↦ (A z).comp (RawInputHilbert.restriction (wideBand n j.val))
  have hS (z : CarrierParameter) (f : CarrierSliceL2 n) :
      S z f =ᵐ[volume] regularizedCarrierSliceIntegral d m z f :=
    carrierSlice_ae_wideRestriction d m z (A z) (hA z)
      (fun η hη x ↦ by simp [maskedCarrierKernel, m, carrierBand, radialBand_eq_zero_off_wideBand hη]) f
  have hSn (z : CarrierParameter) : (S z).comp (S z).adjoint =
      ψ (carrierSamplingEquiv z) • transferOperator
        (atomNormal (wideBandKernelOperator D j.val (j, carrierSamplingEquiv z))) := by
    rw [wideBandRestriction_normal]
    simp only [A, map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hψ.nonneg _), transferOutputOperator_normal]
    rfl
  have hi : Integrable (fun z : Point ↦ ψ z • atomNormal
      (wideBandKernelOperator D j.val (j, z))) :=
    integrable_wideBand_patch_normal D j id continuous_id hψ hc
  have hnormal : T.comp T.adjoint = transferOperator
      (∫ z : Point, ψ z • atomNormal (wideBandKernelOperator D j.val (j, z))) := by
    rw [carrier_normal_eq_sampling_integral d m H T S hT hS,
      transferOperator_sampling_integral _ hi]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hSn]
    simp only [MeasurableEquiv.apply_symm_apply, transferOperator,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have hadj (q : ComplexOutputL2 n) : T.adjoint q =
      c • carrierMultiplier (dyadicCarrierBandMask n j.val) (U.adjoint q) := by
    apply Lp.ext
    filter_upwards [carrier_adjoint_ae_eq_integral d m H T hT q,
      Lp.coeFn_smul c (carrierMultiplier (dyadicCarrierBandMask n j.val) (U.adjoint q)),
      carrierMultiplier_coeFn (dyadicCarrierBandMask n j.val) (U.adjoint q),
      dyadicCarrierBandMask_coeFn n j.val, hU q] with u ht hs hm hb hu
    rw [ht, hs, Pi.smul_apply, hm, hb, hu]
    simp only [maskedCarrierKernel, m, Complex.ofReal_mul, mul_smul, inner_smul_left,
      Complex.conj_ofReal, integral_const_mul, carrierAdjointIntegral,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    ac_rfl
  have hreal : realQuadratureChannel T =
      c • (carrierChannel U).comp (carrierMultiplier (dyadicCarrierBandMask n j.val)) := by
    apply ContinuousLinearMap.adjoint.injective
    rw [map_smul, ContinuousLinearMap.adjoint_comp, carrierMultiplier_adjoint]
    ext1 q
    rw [realQuadratureChannel_adjoint_apply, hadj, smul_apply, ContinuousLinearMap.comp_apply,
      carrierChannel_adjoint_apply, map_smul]
    exact smul_comm _ _ _
  have he := realQuadratureChannel_normal_eq_four_realPart T
  rw [hnormal, realOutputCompression_transferOperator] at he
  have hsmul (K : EuclideanL2 n (Euclidean n) →L[ℝ] EuclideanL2 n (Euclidean n)) :
      transferOperator ((4 : ℝ) • K) = (4 : ℝ) • transferOperator K := by
    simp only [transferOperator, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [hsmul, ← he, hreal, map_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, ← pow_two]

end JanetCartan.CanonicalRowComparison
