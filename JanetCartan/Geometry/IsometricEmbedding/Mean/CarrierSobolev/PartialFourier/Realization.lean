module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Fubini
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FourierCompatibility

/-!
# Partial unitary inverse Fourier realization on carrier L²

The actual `η → y` operator for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse` is the Fubini conjugate of the fiberwise
unitary radian inverse. Both sides are the literal product-measure carrier L²
space. The representative formulas leave `z = (s,v)` unchanged and include
`(synthesisFactor n)⁻¹`. All statements include transverse dimension zero.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
namespace JanetCartan.CarrierSobolev
open ContinuumRow
variable {n : ℕ}

/-- Actual partial unitary radian inverse Fourier equivalence from `(z,η)`
to `(z,y)`, consumed by the initial Sobolev scale in
`app:ch_background:prop:bg-adjoint`. -/
def partialUnitaryInverse (n : ℕ) : CarrierL2 n ≃ₗᵢ[ℂ] CarrierL2 n :=
  ((carrierFubiniEquiv n).trans (iteratedUnitaryInverse n)).trans
    (carrierFubiniEquiv n).symm

/-- Fubini identifies the actual partial transform with the fiberwise one
(`app:ch_background:prop:bg-adjoint`). -/
theorem carrierFubiniEquiv_partialUnitaryInverse (f : CarrierL2 n) :
    carrierFubiniEquiv n (partialUnitaryInverse n f) =
      iteratedUnitaryInverse n (carrierFubiniEquiv n f) :=
  (carrierFubiniEquiv n).apply_symm_apply _

/-- Plancherel on the paper's literal measure `(ds dv) dη`
(`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_norm (f : CarrierL2 n) :
    ‖partialUnitaryInverse n f‖ = ‖f‖ :=
  (partialUnitaryInverse n).norm_map f

/-- Left inverse on all carrier L² classes
(`app:ch_background:prop:bg-inverse`). -/
theorem partialUnitaryInverse_symm_apply_apply (f : CarrierL2 n) :
    (partialUnitaryInverse n).symm (partialUnitaryInverse n f) = f :=
  (partialUnitaryInverse n).symm_apply_apply f

/-- Right inverse on all physical initial L² classes
(`app:ch_background:prop:bg-inverse`). -/
theorem partialUnitaryInverse_apply_symm_apply (f : CarrierL2 n) :
    partialUnitaryInverse n ((partialUnitaryInverse n).symm f) = f :=
  (partialUnitaryInverse n).apply_symm_apply f

/-- Fiberwise representative of the partial transform, without an L¹
assumption (`app:ch_background:prop:bg-adjoint`). The nested a.e. statement
avoids any assumption about joint evaluation of arbitrary L²-valued sections. -/
theorem partialUnitaryInverse_coeFn (f : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun y => partialUnitaryInverse n f (z, y)) =ᵐ[volume]
        transverseUnitaryInverse n ℂ ((carrierFubiniEquiv n f) z) := by
  filter_upwards [carrierFubiniEquiv_symm_coeFn n
    (iteratedUnitaryInverse n (carrierFubiniEquiv n f)),
    iteratedUnitaryInverse_coeFn n (carrierFubiniEquiv n f)] with z hz hz'
  exact hz.trans (Filter.Eventually.of_forall fun y => congrArg (fun g : TransverseL2 n => g y) hz')

/-- The inverse also fixes the outer carrier parameters
(`app:ch_background:prop:bg-inverse`). -/
theorem partialUnitaryInverse_symm_coeFn (f : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun η => (partialUnitaryInverse n).symm f (z, η)) =ᵐ[volume]
        (transverseUnitaryInverse n ℂ).symm ((carrierFubiniEquiv n f) z) := by
  filter_upwards [carrierFubiniEquiv_symm_coeFn n
    ((iteratedUnitaryInverse n).symm (carrierFubiniEquiv n f)),
    iteratedUnitaryInverse_symm_coeFn n (carrierFubiniEquiv n f)] with z hz hz'
  exact hz.trans (Filter.Eventually.of_forall fun η => congrArg (fun g : TransverseL2 n => g η) hz')

/-- Ordinary inverse-integral representative on data with integrable slices,
including its exact unitary normalization
(`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_integral (f : CarrierL2 n)
    (hf : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η => f (z, η)) volume) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun y => partialUnitaryInverse n f (z, y)) =ᵐ[volume]
        unitaryInverseIntegral (fun η => f (z, η)) := by
  filter_upwards [partialUnitaryInverse_coeFn f, carrierFubiniEquiv_coeFn n f, hf]
    with z hz he hi
  refine hz.trans ((transverseUnitaryInverse_coeFn _ (hi.congr he.symm)).trans ?_)
  exact Filter.Eventually.of_forall fun y => by
    simp only [unitaryInverseIntegral, radianInverseIntegral_eq_fourierInv]
    rw [Real.fourierInv_congr_ae he]

/-- Formula for a specified L² representative with almost every slice in L¹
(`app:ch_background:prop:bg-adjoint`). The L² and L¹ hypotheses are analytic
membership conditions, not assumptions about the transform's action. -/
theorem partialUnitaryInverse_toLp {f : CarrierVariable n → ℂ}
    (h₂ : MemLp f 2 (carrierMeasure n))
    (h₁ : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η => f (z, η)) volume) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun y => partialUnitaryInverse n (h₂.toLp f) (z, y)) =ᵐ[volume]
        unitaryInverseIntegral (fun η => f (z, η)) := by
  have he := MeasureTheory.Measure.ae_ae_of_ae_prod h₂.coeFn_toLp
  have hi : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η => (h₂.toLp f) (z, η)) volume := by
    filter_upwards [h₁, he] with z hz hez
    exact hz.congr (Filter.EventuallyEq.symm hez)
  filter_upwards [partialUnitaryInverse_integral (h₂.toLp f) hi, he] with z hz hez
  refine hz.trans (Filter.Eventually.of_forall fun y => ?_)
  simp only [unitaryInverseIntegral, radianInverseIntegral_eq_fourierInv]
  rw [Real.fourierInv_congr_ae hez]

/-- Compact continuous, hence compact smooth, product-space tests satisfy the
literal inverse-integral formula with every outer parameter retained
(`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_compact_test {f : CarrierVariable n → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (fun y => partialUnitaryInverse n ((hf.memLp_of_hasCompactSupport (p := 2) (μ := (volume.prod volume).prod volume) hc).toLp f)
        (z, y)) =ᵐ[volume] unitaryInverseIntegral (fun η => f (z, η)) := by
  apply partialUnitaryInverse_toLp
  apply Filter.Eventually.of_forall
  intro z
  apply (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro η hη
  exact ⟨(z, η), subset_tsupport f hη, rfl⟩

/-- Joint measurability of the ordinary partial inverse integral for a
measurable product-space representative. This is used to turn the nested
formula into product almost-everywhere equality
(`app:ch_background:prop:bg-adjoint`). -/
theorem stronglyMeasurable_partialUnitaryIntegral {f : CarrierVariable n → ℂ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun p : CarrierVariable n =>
      unitaryInverseIntegral (fun η => f (p.1, η)) p.2) := by
  have hk : Continuous (fun q : CarrierVariable n × Euclidean (n - 1) =>
      Complex.exp ((inner ℝ q.2 q.1.2 : ℂ) * Complex.I)) := by fun_prop
  have hm : StronglyMeasurable (fun q : CarrierVariable n × Euclidean (n - 1) =>
      Complex.exp ((inner ℝ q.2 q.1.2 : ℂ) * Complex.I) • f (q.1.1, q.2)) :=
    hk.stronglyMeasurable.smul
      (hf.comp_measurable (measurable_fst.fst.prodMk measurable_snd))
  exact hm.integral_prod_right'.const_smul _

/-- Literal product-space representative formula on measurable L² data with
integrable slices (`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_toLp_ae {f : CarrierVariable n → ℂ}
    (hm : StronglyMeasurable f) (h₂ : MemLp f 2 (carrierMeasure n))
    (h₁ : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η => f (z, η)) volume) :
    partialUnitaryInverse n (h₂.toLp f) =ᵐ[carrierMeasure n]
      fun p => unitaryInverseIntegral (fun η => f (p.1, η)) p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (stronglyMeasurable_partialUnitaryIntegral hm).measurable)).mpr
  exact partialUnitaryInverse_toLp h₂ h₁

/-- Compact smooth product-space tests, and even compact continuous tests,
have the paper's actual partial integral representative. In particular
`unitaryInverseIntegral` includes `(synthesisFactor n)⁻¹`
(`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_compact_test_ae {f : CarrierVariable n → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    partialUnitaryInverse n
        ((hf.memLp_of_hasCompactSupport (p := 2) (μ := (volume.prod volume).prod volume) hc).toLp f)
      =ᵐ[carrierMeasure n] fun p => unitaryInverseIntegral (fun η => f (p.1, η)) p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (stronglyMeasurable_partialUnitaryIntegral hf.stronglyMeasurable).measurable)).mpr
  exact partialUnitaryInverse_compact_test hf hc

/-- Squared norm preservation on the literal product measure, used by the
order-zero carrier input scale (`app:ch_background:prop:bg-adjoint`). -/
theorem partialUnitaryInverse_integral_norm_sq (f : CarrierL2 n) :
    (∫ p, ‖partialUnitaryInverse n f p‖ ^ 2 ∂carrierMeasure n) =
      ∫ p, ‖f p‖ ^ 2 ∂carrierMeasure n := by
  rw [← Fubini.norm_sq, ← Fubini.norm_sq, partialUnitaryInverse_norm]

end JanetCartan.CarrierSobolev
