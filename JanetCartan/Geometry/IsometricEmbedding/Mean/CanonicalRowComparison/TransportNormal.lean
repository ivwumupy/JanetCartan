module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.TransportBand
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.BoundedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Restriction

/-!
# Construct the continuum normal of the literal transport sampling band

The forward kernel identity in `TransportBand` supplies compact kernel bounds
and the actual bounded continuum operator, with the ORIGINAL carrier weight,
smooth band and Fourier normalization. Slice adjoints and normal disintegration
are then consequences, not assumptions. Source:
`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CanonicalRowComparison

open ContinuumRow CurrentMean Sampling Sampling.RawKernel Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition PeriodicLocalL2 AmplitudeBound SeparatedSampling

/-- The precise continuum mask forced by one weighted transport band:
the sample weight enters through its square root, and the physical Fourier
scalar is retained (`app:ch_waves:eq:sampling-prefix-normal`). -/
def transportBandMask (n j : ℕ) (ψ : Point → ℝ) (u : CarrierVariable n) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.sqrt (ψ (carrierSamplingEquiv u.1)) *
    carrierBand n j u

set_option backward.isDefEq.respectTransparency true

/-- The literal weighted sampling kernel supplies the existing finite carrier
kernel bounds on the original measure. This permits the native sampling
constructor to store its detector in `mask`, without changing that constructor
or assuming a continuum operator identity. Consumer: the native transport
normal in `app:ch_waves:eq:colored-normal-comparison`. -/
def weightedSamplingBandFiniteKernelBounds {n N bands : ℕ}
    (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (D : BandKernelData (Fin bands × Point) n) (j : Fin bands)
    (hDzero : ∀ z η, η ∉ wideBand n j.val → ∀ x, D.kernel (j, z) η x = 0)
    (ψ : Point → ℝ) {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ)
    (hkernel : ∀ x u, maskedCarrierKernel d m x u =
      Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
        D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x)) :
    FiniteCarrierKernelBounds d m := by
  let Z : Set CarrierParameter :=
    carrierSamplingEquiv.symm '' Set.Icc (fun _ : Fin 3 ↦ -B) (fun _ ↦ B)
  let R : ℝ := 4 * dyadicScale j.val
  let bound : ℝ := Real.sqrt P * (Real.sqrt R * D.maskBound * D.amplitudeBound)
  have hZ : IsCompact Z :=
    isCompact_Icc.image carrierSamplingLinearEquiv.symm.toContinuousLinearEquiv.continuous
  have hR : 0 ≤ R := by dsimp [R, dyadicScale]; positivity
  have hbc : 0 ≤ bound := mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) D.maskBound_nonneg)
      D.amplitudeBound_nonneg)
  refine ⟨Z, hZ, R, hR, bound, hbc, ?_, ?_, ?_⟩
  · simp_rw [hkernel]
    have hmap : Measurable (fun p : Torus n × CarrierVariable n ↦
        (((j, carrierSamplingEquiv p.2.1), p.2.2), centeredTorusRepresentative p.1)) :=
      (((measurable_const.prodMk (carrierSamplingEquiv.measurable.comp
        measurable_snd.fst)).prodMk measurable_snd.snd).prodMk
          (measurable_centeredTorusRepresentative.comp measurable_fst))
    have hw : StronglyMeasurable (fun p : Torus n × CarrierVariable n ↦
        Real.sqrt (ψ (carrierSamplingEquiv p.2.1))) :=
      (Real.continuous_sqrt.comp hc).stronglyMeasurable.comp_measurable
        (carrierSamplingEquiv.measurable.comp measurable_snd.fst)
    have hk : StronglyMeasurable (fun p : Torus n × CarrierVariable n ↦
        D.kernel (j, carrierSamplingEquiv p.2.1) p.2.2
          (centeredTorusRepresentative p.1)) :=
      (D.continuous_kernel.measurable.comp hmap).stronglyMeasurable
    exact hw.smul hk
  · intro x u
    rw [hkernel]
    by_cases hu : u.2 ∈ wideBand n j.val
    · have hr : ‖u.2‖ ≤ R := by simpa only [wideBand, Set.mem_sdiff,
        Metric.mem_closedBall, dist_zero_right, R] using hu.1
      have hb : ‖D.kernel (j, carrierSamplingEquiv u.1) u.2
          (centeredTorusRepresentative x)‖ ≤
          Real.sqrt R * D.maskBound * D.amplitudeBound := by
        simp only [BandKernelData.kernel, bandKernel, norm_smul, norm_mul,
          Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
        exact mul_le_mul (mul_le_mul (Real.sqrt_le_sqrt hr) (D.mask_le _)
          (norm_nonneg _) (Real.sqrt_nonneg _)) (D.amplitude_le _ _ _)
          (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) D.maskBound_nonneg)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul (Real.sqrt_le_sqrt (hψ.le_bound _)) hb (norm_nonneg _)
        (Real.sqrt_nonneg _)
    · rw [hDzero _ _ hu, smul_zero, norm_zero]
      exact hbc
  · intro x z η hzero
    rw [hkernel]
    rcases hzero with hz | hη
    · have hz0 : ψ (carrierSamplingEquiv z) = 0 := by
        by_contra hz0
        apply hz
        refine ⟨carrierSamplingEquiv z, ?_, carrierSamplingEquiv.symm_apply_apply z⟩
        exact ⟨fun i ↦ (abs_le.mp (hψ.support _ hz0 i)).1,
          fun i ↦ (abs_le.mp (hψ.support _ hz0 i)).2⟩
      simp [hz0]
    · have hηwide : η ∉ wideBand n j.val := by
        intro hh
        have : ‖η‖ ≤ R := by simpa only [wideBand, Set.mem_sdiff,
          Metric.mem_closedBall, dist_zero_right, R] using hh.1
        exact (not_le.mpr hη) this
      rw [hDzero _ _ hηwide, smul_zero]

set_option backward.isDefEq.respectTransparency false

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

local notation "D₀" => transportCrossBandKernelData (bands := bands) d C Yext hY hA K hK hsupport M hM hbound

include hpoint hC hphase in
/-- The same kernel carries the square root of the supplied sampling weight;
this equality keeps all zero weights without division
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem maskedCarrierKernel_transportBandMask (j : Fin bands) (ψ : Point → ℝ)
    (x : Torus n) (u : CarrierVariable n) :
    maskedCarrierKernel d (transportBandMask n j.val ψ) x u =
      Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
        (D₀).kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x) := by
  rw [transportCrossBandKernelData_kernel_on_torus d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase]
  simp only [maskedCarrierKernel, transportBandMask, carrierBand,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  simp only [mul_comm, mul_left_comm, mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency true

include hpoint hC hphase in
/-- Compactness and boundedness of the constructed transport kernel discharge
the existing disintegration interface. No finite-normal or adjoint estimate
is assumed. The bounds here are only used for integrability; the sharper
oscillatory bounds remain the sampling producer's inputs
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def transportBandFiniteKernelBounds (j : Fin bands) (ψ : Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    FiniteCarrierKernelBounds d (transportBandMask n j.val ψ) :=
  weightedSamplingBandFiniteKernelBounds d (transportBandMask n j.val ψ) D₀ j
    (fun z η hη x ↦ transportCrossBandKernelData_eq_zero_off_wideBand
      d C Yext hY hA K hK hsupport M hM hbound j z η x hη) ψ hψ hc
    (maskedCarrierKernel_transportBandMask d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase j ψ)

set_option backward.isDefEq.respectTransparency false

/-- The continuum band operator is CONSTRUCTED from the identical kernel
and weight, on the original carrier measure. This instantiates the existing
bounded-kernel construction, not a new canonical record
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`). -/
def transportBandContinuumOperator (j : Fin bands) (ψ : Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    CarrierL2 n →L[ℂ] ComplexOutputL2 n :=
  let h := transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase j ψ hψ hc
  CarrierRegularization.boundedKernelOperator
    (K := maskedCarrierKernel d (transportBandMask n j.val ψ)) h.stronglyMeasurable
    h.isCompact_initialSupport.measurableSet h.isCompact_initialSupport.measure_lt_top.ne
    h.kernel_eq_zero_off_initialSupport h.norm_le

/-- The constructed continuum operator has its literal forward integral,
with its original masks and product measure
(`app:ch_background:eq:bg-T`). -/
theorem transportBandContinuumOperator_ae (j : Fin bands) (ψ : Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) (f : CarrierL2 n) :
    transportBandContinuumOperator d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase j ψ hψ hc f
      =ᵐ[volume] regularizedCarrierIntegral d (transportBandMask n j.val ψ) f := by
  let h := transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound
    hpoint hC hphase j ψ hψ hc
  filter_upwards [CarrierRegularization.boundedKernelOperator_ae
    (K := maskedCarrierKernel d (transportBandMask n j.val ψ)) h.stronglyMeasurable
    h.isCompact_initialSupport.measurableSet h.isCompact_initialSupport.measure_lt_top.ne
    h.kernel_eq_zero_off_initialSupport h.norm_le f] with x hx
  exact hx.trans (regularizedCarrierIntegral_eq_masked d _ f x).symm

/-- Wide-band restriction followed by its literal adjoint is the identity;
there is no loss of either annular quadrature in the transport normal
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem wideBandRestriction_normal {n j : ℕ}
    (A : WideBandL2 n j →L[ℂ] ComplexOutputL2 n) :
    (A.comp (RawInputHilbert.restriction (wideBand n j))).comp
      (A.comp (RawInputHilbert.restriction (wideBand n j))).adjoint = A.comp A.adjoint := by
  let e := RawInputHilbert.zeroExtension (μ := (volume : Measure (Euclidean (n - 1))))
    (measurableSet_wideBand n j)
  have he : (RawInputHilbert.restriction (μ := (volume : Measure (Euclidean (n - 1))))
      (wideBand n j)).comp (RawInputHilbert.restriction (wideBand n j)).adjoint =
      ContinuousLinearMap.id ℂ (WideBandL2 n j) := by
    rw [← RawInputHilbert.adjoint_zeroExtension (measurableSet_wideBand n j),
      ContinuousLinearMap.adjoint_adjoint]
    exact e.adjoint_comp_self
  rw [ContinuousLinearMap.adjoint_comp]
  ext1 f
  change A ((RawInputHilbert.restriction (wideBand n j)).comp
    (RawInputHilbert.restriction (wideBand n j)).adjoint (A.adjoint f)) = A (A.adjoint f)
  rw [he]
  rfl

/-- The original smooth band removes the wide restriction from its forward
integral, on the same full transverse measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrierSlice_ae_wideRestriction {n N j : ℕ}
    (d : CarrierData n N) (m : CarrierVariable n → ℝ)
    (z : CarrierParameter) (A : WideBandL2 n j →L[ℂ] ComplexOutputL2 n)
    (hA : ∀ f, A f =ᵐ[volume] regularizedCarrierSliceIntegral d m z f)
    (hz : ∀ η ∉ wideBand n j, ∀ x, maskedCarrierKernel d m x (z, η) = 0)
    (f : CarrierSliceL2 n) :
    A (RawInputHilbert.restriction (wideBand n j) f) =ᵐ[volume]
      regularizedCarrierSliceIntegral d m z f := by
  filter_upwards [hA (RawInputHilbert.restriction (wideBand n j) f)] with x hx
  rw [hx]
  unfold regularizedCarrierSliceIntegral
  conv_lhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun η hη ↦ by rw [hz η hη x, smul_zero])]
  conv_rhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun η hη ↦ by rw [hz η hη x, smul_zero])]
  apply integral_congr_ae
  filter_upwards [RawInputHilbert.restriction_coeFn (wideBand n j) f] with η hη
  rw [hη]

/-- The actual weighted transport slice acts on the original full transverse
L² space by the original wide-band restriction. Its weight may be zero;
no inverse weight is used (`app:ch_waves:eq:sampling-prefix-normal`). -/
def transportBandSliceOperator (j : Fin bands) (ψ : Point → ℝ) (z : CarrierParameter) :
    CarrierSliceL2 n →L[ℂ] ComplexOutputL2 n :=
  (Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ) •
    (transferOutputOperator (wideBandKernelOperator D₀ j.val
      (j, carrierSamplingEquiv z))).comp (RawInputHilbert.restriction (wideBand n j.val))

include hpoint hC hphase in
/-- The constructed slice has the identical continuum forward kernel. The
restriction disappears only because the ORIGINAL smooth band vanishes on
its complement (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transportBandSliceOperator_ae (j : Fin bands) (ψ : Point → ℝ)
    (z : CarrierParameter) (f : CarrierSliceL2 n) :
    transportBandSliceOperator d C Yext hY hA K hK hsupport M hM hbound j ψ z f =ᵐ[volume]
      regularizedCarrierSliceIntegral d (transportBandMask n j.val ψ) z f := by
  let m₀ := fun u : CarrierVariable n ↦
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * carrierBand n j.val u
  let A := transferOutputOperator (wideBandKernelOperator D₀ j.val (j, carrierSamplingEquiv z))
  have hzero (η) (hη : η ∉ wideBand n j.val) (x : Torus n) :
      maskedCarrierKernel d m₀ x (z, η) = 0 := by
    simp [maskedCarrierKernel, m₀, carrierBand, radialBand_eq_zero_off_wideBand hη]
  have hf := carrierSlice_ae_wideRestriction d m₀ z A
    (transportCrossBandKernelData_wideOperator_ae_slice d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase j z) hzero f
  filter_upwards [hf, Lp.coeFn_smul (Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ)
    (A (RawInputHilbert.restriction (wideBand n j.val) f))] with x hx hs
  change ((Real.sqrt (ψ (carrierSamplingEquiv z)) : ℂ) •
    A (RawInputHilbert.restriction (wideBand n j.val) f)) x = _
  rw [hs, Pi.smul_apply, hx]
  simp only [regularizedCarrierSliceIntegral, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [maskedCarrierKernel, m₀, transportBandMask, carrierBand, smul_smul]
  congr 1
  push_cast
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The adjoint of the literal wide restriction is zero extension. Therefore
its normal has exactly the supplied carrier weight and the original output
transfer, without inverse weights or discarded quadratures
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transportBandSliceOperator_normal (j : Fin bands) (ψ : Point → ℝ)
    (z : CarrierParameter) (hψ : 0 ≤ ψ (carrierSamplingEquiv z)) :
    let A := transportBandSliceOperator d C Yext hY hA K hK hsupport M hM hbound j ψ z
    A.comp A.adjoint = ψ (carrierSamplingEquiv z) • transferOperator
      (atomNormal (wideBandKernelOperator D₀ j.val (j, carrierSamplingEquiv z))) := by
  dsimp only
  simp only [transportBandSliceOperator, map_smulₛₗ, Complex.conj_ofReal,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hψ]
  rw [wideBandRestriction_normal, transferOutputOperator_normal]
  rfl

/-- The weighted transport sampling normal is the normal of the CONSTRUCTED
continuum band on the same carrier measure. All forward formulas, adjoints,
compact bounds and Bochner integrability are discharged above and by the
existing disintegration theorem (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem transportBandContinuumOperator_normal (j : Fin bands) (ψ : Point → ℝ)
    {B P : ℝ} (hψ : PatchBounds ψ B P) (hc : Continuous ψ) :
    let T := transportBandContinuumOperator d C Yext hY hA K hK hsupport M hM hbound
      hpoint hC hphase j ψ hψ hc
    T.comp T.adjoint = ∫ z : Point, ψ z • transferOperator
      (atomNormal (wideBandKernelOperator D₀ j.val (j, z))) := by
  dsimp only
  rw [carrier_normal_eq_sampling_integral d (transportBandMask n j.val ψ)
    (transportBandFiniteKernelBounds d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase j ψ hψ hc)
    _ (transportBandSliceOperator d C Yext hY hA K hK hsupport M hM hbound j ψ)
    (transportBandContinuumOperator_ae d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase j ψ hψ hc)
    (transportBandSliceOperator_ae d C Yext hY hA K hK hsupport M hM hbound hpoint hC hphase j ψ)]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [MeasurableEquiv.apply_symm_apply] using
    transportBandSliceOperator_normal d C Yext hY hA K hK hsupport M hM hbound j ψ
      (carrierSamplingEquiv.symm z) (by simpa using hψ.nonneg z)

end JanetCartan.CanonicalRowComparison
