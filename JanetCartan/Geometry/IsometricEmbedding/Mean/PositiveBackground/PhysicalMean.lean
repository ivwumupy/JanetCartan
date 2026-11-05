module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CarrierMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Mean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.TransportedDensity

/-!
# The literal physical mean of the positive density

For `app:ch_background:eq:bg-affine-mean`, keep the original normal, footpoint,
covector, and external squared weight. Its physical tensor mean is affine in
the uncut density. On the measurement plateau, contraction of its increment
is exactly `UncutDensity.measuredIncrement`, with no additional factor.

This connects the physical tensor in `app:ch_background:eq:bg-current-identity`
to `PositiveBackground.exists_smooth_physical_background_cancellation`. The
continuity inputs below are local carrier geometry, not a mean identity or an
inverse estimate. The weight is supplied and is never reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow UncutDensity NormalizedBackground CurrentMean

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal physical tensor `H_G[σ²(1+v)]` of
`app:ch_background:eq:bg-affine-mean`. The original normal in `d` already
contains initial scalar `σ`; the external measure is exactly `χ² dz`. -/
def physicalDensityMean (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (v : ι → CarrierVariable n → ℝ) : MetricField n :=
  fun x ↦ ∑ a, fun i j ↦ ∫ z,
    (χ a z ^ 2 * (1 + v a (z, (d a).transportedPosition x z))) *
      ‖(d a).normalField x z‖ ^ 2 *
        ((d a).covector x z i * (d a).covector x z j) ∂(volume.prod volume)

/-- Zero density is exactly the original mean of the supplied retained
normal and covector, with the SAME weights and measure. This is the mean
used by `RetainedAssembly.NormalizedMeanSource`
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-current-raising`). -/
@[simp] theorem physicalDensityMean_zero (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) :
    physicalDensityMean d χ 0 = carrierMean (fun _ ↦ volume.prod volume)
      (fun a z ↦ χ a z ^ 2) (fun a p ↦ (d a).normalField p.1 p.2)
      (fun a p ↦ (d a).covector p.1 p.2) := by
  funext x
  unfold physicalDensityMean carrierMean
  simp only [Pi.zero_apply, add_zero, mul_one]

/-- The density formula is the actual normal square after multiplication by
`sqrt (1+v(z,Y))`, as supplied by scalar-transport linearity for the positive
initial amplitude. No Fourier or response factor enters the mean
(`app:ch_background:eq:bg-affine-mean`). -/
theorem physicalDensityMean_eq_carrierMean (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (v : ι → CarrierVariable n → ℝ)
    (hv : ∀ a p, 0 ≤ 1 + v a p) :
    physicalDensityMean d χ v = carrierMean (fun _ ↦ volume.prod volume)
      (fun a z ↦ χ a z ^ 2)
      (fun a p ↦ Real.sqrt (1 + v a (p.2, (d a).transportedPosition p.1 p.2)) •
        (d a).normalField p.1 p.2) (fun a p ↦ (d a).covector p.1 p.2) := by
  funext x
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply integral_congr_ae
  filter_upwards [] with z
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hv a _)]
  ring

/-- Smoothness of the uncorrected physical mean follows from the supplied
retained fields on their original carrier neighborhoods. This supplies the
source regularity for `physicalDensityMean_uncorrected_core_cancellation`
(`app:ch_background:eq:bg-current-raising`). -/
theorem contDiffOn_physicalDensityMean_zero (d : ι → CarrierData n N)
    (χ : ι → CarrierParameter → ℝ) (hχ : ∀ a, ContDiff ℝ ∞ (χ a))
    (hχc : ∀ a, HasCompactSupport (χ a))
    {W : Set (Euclidean n)} (hW : IsOpen W)
    (V : ι → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hχV : ∀ a, tsupport (χ a) ⊆ V a)
    (hν : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).normalField p.1 p.2) (W ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (fun p ↦ (d a).covector p.1 p.2) (W ×ˢ V a)) :
    ContDiffOn ℝ ∞ (physicalDensityMean d χ 0) W := by
  let (a : ι) : IsFiniteMeasure ((volume.prod volume).restrict (tsupport (χ a))) :=
    ⟨by simpa using (hχc a).measure_lt_top (μ := volume.prod volume)⟩
  rw [physicalDensityMean_zero]
  unfold carrierMean
  apply ContDiffOn.sum
  intro a _
  let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have he : (fun x ↦ ∫ z, χ a z ^ 2 * ‖(d a).normalField x z‖ ^ 2 *
        ((d a).covector x z i * (d a).covector x z j) ∂(volume.prod volume)) =
      fun x ↦ ∫ z in tsupport (χ a), χ a z ^ 2 * ‖(d a).normalField x z‖ ^ 2 *
        ((d a).covector x z i * (d a).covector x z j) ∂(volume.prod volume) := by
    funext x
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [he]
  exact contDiffOn_compactParameterIntegral hW (hV a) (hχc a) (hχV a)
    (SourceGeometry.contDiffOn_carrierMean_integrand ((hχ a).pow 2 |>.contDiffOn)
      (hν a) (hξ a) i j)

private theorem integrable_density_entry (d : CarrierData n N)
    (χ : CarrierParameter → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : CarrierVariable n → ℝ) (hv : Continuous v) (x : Euclidean n)
    (hY : ContinuousOn (d.transportedPosition x) (tsupport χ))
    (hν : ContinuousOn (d.normalField x) (tsupport χ))
    (hξ : ContinuousOn (d.covector x) (tsupport χ)) (i j : Fin n) :
    Integrable (fun z ↦ χ z ^ 2 * v (z, d.transportedPosition x z) *
      ‖d.normalField x z‖ ^ 2 * (d.covector x z i * d.covector x z j))
      (volume.prod volume) := by
  have hcoord (i : Fin n) : ContinuousOn (fun z ↦ d.covector x z i) (tsupport χ) :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn hξ
  have hc := (((hχ.continuousOn.pow 2).mul
    (hv.comp_continuousOn (continuousOn_id.prodMk hY))).mul
      (hν.norm.pow 2)).mul ((hcoord i).mul (hcoord j))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (hc.integrableOn_compact' hχc (isClosed_tsupport χ).measurableSet)
  intro z hz
  by_contra h
  apply hz
  simp [image_eq_zero_of_notMem_tsupport h]

private theorem tensorPairing_integral_entries (Q : MetricTensor n)
    (f : CarrierParameter → MetricTensor n)
    (hf : ∀ i j, Integrable (fun z ↦ f z i j) (volume.prod volume)) :
    tensorPairing Q (fun i j ↦ ∫ z, f z i j ∂(volume.prod volume)) =
      ∫ z, tensorPairing Q (f z) ∂(volume.prod volume) := by
  simp only [tensorPairing]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _
    (fun j _ ↦ (hf i j).const_mul (Q i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ (hf i j).const_mul (Q i j))]
  simp only [integral_const_mul]

/-- The physical tensor increment contracts to precisely the same row's
measured increment on its physical plateau. Integrability is proved from
the original compact weight and continuous fields, and the factor is one
(`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_eq_physicalDensityMean_sub
    (d : ι → CarrierData n N) (χ : ι → CarrierParameter → ℝ)
    (hχ : ∀ a, Continuous (χ a)) (hχc : ∀ a, HasCompactSupport (χ a))
    (v : ι → CarrierVariable n → ℝ) (hv : ∀ a, Continuous (v a))
    (x : Euclidean n) (Q : Fin n → MetricTensor n)
    (hY : ∀ a, ContinuousOn ((d a).transportedPosition x) (tsupport (χ a)))
    (hν : ∀ a, ContinuousOn ((d a).normalField x) (tsupport (χ a)))
    (hξ : ∀ a, ContinuousOn ((d a).covector x) (tsupport (χ a)))
    (hchart : ∀ a, torusQuotient x ∈ (d a).outputChart)
    (hpoint : ∀ a, (d a).chartPoint (torusQuotient x) = x)
    (hmeas : ∀ a, (d a).measurementCutoff (torusQuotient x) = 1)
    (hQ : ∀ a i, (d a).stressFrame x i = Q i) (i : Fin n) :
    (∑ a, measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x)) i =
      tensorPairing (Q i) (physicalDensityMean d χ v x - physicalDensityMean d χ 0 x) := by
  classical
  let f : ι → CarrierParameter → MetricTensor n := fun a z j k ↦
    χ a z ^ 2 * v a (z, (d a).transportedPosition x z) *
    ‖(d a).normalField x z‖ ^ 2 * ((d a).covector x z j * (d a).covector x z k)
  have hf (a : ι) (j k : Fin n) : Integrable (fun z ↦ f a z j k) (volume.prod volume) :=
    integrable_density_entry (d a) (χ a) (hχ a) (hχc a) (v a) (hv a) x
      (hY a) (hν a) (hξ a) j k
  have he : physicalDensityMean d χ v x - physicalDensityMean d χ 0 x =
      ∑ a, fun j k ↦ ∫ z, f a z j k ∂(volume.prod volume) := by
    rw [physicalDensityMean, physicalDensityMean, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ext j k
    have hb := integrable_density_entry (d a) (χ a) (hχ a) (hχc a)
      (fun _ ↦ 1) continuous_const x (hY a) (hν a) (hξ a) j k
    simp only [mul_one] at hb
    simp only [Pi.zero_apply, add_zero, mul_one, Matrix.sub_apply]
    simp_rw [mul_add, mul_one, add_mul]
    rw [integral_add hb (hf a j k), add_sub_cancel_left]
  rw [he]
  change (EuclideanSpace.proj i) (∑ a,
    measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x)) = _
  rw [map_sum]
  have hpair (f : ι → MetricTensor n) : tensorPairing (Q i) (∑ a, f a) =
      ∑ a, tensorPairing (Q i) (f a) := by
    let L : MetricTensor n →ₗ[ℝ] ℝ :=
      { toFun := tensorPairing (Q i)
        map_add' := by intros; simp [tensorPairing, mul_add, Finset.sum_add_distrib]
        map_smul' := by intros; simp [tensorPairing, Finset.mul_sum, mul_left_comm] }
    exact map_sum L _ _
  rw [hpair]
  apply Finset.sum_congr rfl
  intro a _
  change measuredIncrement (d a) (fun z ↦ χ a z ^ 2) (v a) (torusQuotient x) i =
    tensorPairing (Q i) (fun j k ↦ ∫ z, f a z j k ∂(volume.prod volume))
  rw [tensorPairing_integral_entries _ _ (hf a)]
  have hS : ContinuousOn (measuredStress (d a) (torusQuotient x)) (tsupport (χ a)) := by
    rw [show measuredStress (d a) (torusQuotient x) =
        fun z ↦ ‖(d a).normalField x z‖ ^ 2 • reducedCovector (d a) x ((d a).covector x z) from by
      funext z; simp only [measuredStress, hpoint a, hmeas a, one_mul]]
    apply (hν a).norm.pow 2 |>.smul
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro l
    change ContinuousOn (fun z ↦ ∑ j, ∑ k,
      (d a).stressFrame x l j k * ((d a).covector x z j * (d a).covector x z k)) _
    exact continuousOn_finsetSum _ fun j _ ↦ continuousOn_finsetSum _ fun k _ ↦
      continuousOn_const.mul (((EuclideanSpace.proj j).continuous.comp_continuousOn (hξ a)).mul
        ((EuclideanSpace.proj k).continuous.comp_continuousOn (hξ a)))
  have hInt : Integrable (fun z ↦
      (χ a z ^ 2 * v a (z, (d a).transportedPosition ((d a).chartPoint (torusQuotient x)) z)) •
        measuredStress (d a) (torusQuotient x) z) (volume.prod volume) := by
    rw [hpoint a]
    have hc := ((hχ a).continuousOn.pow 2 |>.mul
      ((hv a).comp_continuousOn (continuousOn_id.prodMk (hY a)))).smul hS
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (hc.integrableOn_compact' (hχc a) (isClosed_tsupport (χ a)).measurableSet)
    intro z hz
    by_contra h
    apply hz
    simp [image_eq_zero_of_notMem_tsupport h]
  rw [measuredIncrement, indicator_of_mem (hchart a)]
  have heval := (EuclideanSpace.proj i).integral_comp_comm hInt
  change (∫ z, ((χ a z ^ 2 * v a
    (z, (d a).transportedPosition ((d a).chartPoint (torusQuotient x)) z)) •
      measuredStress (d a) (torusQuotient x) z) i ∂(volume.prod volume)) = _ at heval
  refine heval.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PiLp.smul_apply, smul_eq_mul, measuredStress,
    hpoint a, hmeas a, one_mul, reducedCovector, hQ a i, tensorPairing,
    f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end JanetCartan.PositiveBackground
