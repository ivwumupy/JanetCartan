module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.Zero
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FullCompatibility

/-!
# Transverse weighted Plancherel on compact tests

The transverse part of `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. Parameter Fourier commutes with
multiplication by the bounded reciprocal Bessel weight. Applying that identity
to the weighted test recovers the unbounded weighted identity, with the actual
radian dilation and literal product measure, including transverse dimension zero.
The consumer is `partialUnitaryInverse_test_sobolev_bound_of_split_estimates`.
-/

set_option maxHeartbeats 2000000

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

private theorem etaWeight_one_le (s : ℕ) (η : Euclidean (n - 1)) :
    1 ≤ etaBesselWeight s ((0 : CarrierParameter), η) := by
  simpa [etaBesselWeight] using
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖η‖])) s

private theorem etaWeight_ne_zero (s : ℕ) (η : Euclidean (n - 1)) :
    etaBesselWeight s ((0 : CarrierParameter), η) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (etaWeight_one_le s η))

private theorem transverseWeight_rescale (s : ℕ) (ξ : Euclidean (n - 1)) :
    initialWeight s ((0 : CarrierParameter), ξ) =
      etaBesselWeight s ((0 : CarrierParameter), (2 * Real.pi) • ξ) := by
  rw [initialWeight_eq_coordinates]
  simp only [Prod.fst_zero, Prod.snd_zero, abs_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, etaBesselWeight, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_pow]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ s, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

private theorem reciprocalWeightMemLp (s : ℕ) :
    MemLp (fun η : Euclidean (n - 1) =>
      Complex.ofReal ((etaBesselWeight s ((0 : CarrierParameter), η))⁻¹)) ⊤ volume := by
  refine memLp_top_of_bound ?_ 1 ?_
  · exact (Complex.continuous_ofReal.comp
      (((continuous_etaBesselWeight s).comp (continuous_const.prodMk continuous_id)).inv₀
        (etaWeight_ne_zero s))).aestronglyMeasurable
  · exact Eventually.of_forall fun η => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (etaBesselWeight_nonneg s _))]
      exact inv_le_one_of_one_le₀ (etaWeight_one_le s η)

private def reciprocalWeightOperator (s : ℕ) : TransverseL2 n →L[ℂ] TransverseL2 n :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ⊤ 2 2
    ((reciprocalWeightMemLp (n := n) s).toLp _)

private theorem reciprocalWeightOperator_coeFn (s : ℕ) (g : TransverseL2 n) :
    reciprocalWeightOperator s g =ᵐ[volume]
      fun η => (etaBesselWeight s ((0 : CarrierParameter), η))⁻¹ • g η := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
    ((reciprocalWeightMemLp (n := n) s).toLp _) g,
    (reciprocalWeightMemLp (n := n) s).coeFn_toLp] with η hη hw
  rw [show reciprocalWeightOperator s g η = _ from hη, hw]
  rfl

private theorem weighted_fourier_synthesis_coeFn (s : ℕ) (u h : CarrierL2 n)
    (hh : h =ᵐ[carrierMeasure n] fun x => etaBesselWeight s x • u x) :
    (fun ξ : CarrierVariable n => initialWeight s ((0 : CarrierParameter), ξ.2) •
      initialFourier n (partialUnitaryInverse n u) ξ) =ᵐ[carrierMeasure n]
        initialFourier n (partialUnitaryInverse n h) := by
  let L : TransverseL2 n →L[ℂ] TransverseL2 n := reciprocalWeightOperator s
  have hinput : L.compLp (carrierFubiniEquiv n h) = carrierFubiniEquiv n u := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLp (carrierFubiniEquiv n h),
      carrierFubiniEquiv_coeFn n h, carrierFubiniEquiv_coeFn n u,
      ae_ae_of_ae_prod hh] with z hz hhz huz hw
    rw [hz]
    apply Lp.ext
    filter_upwards [reciprocalWeightOperator_coeFn s ((carrierFubiniEquiv n h) z),
      hhz, huz, hw] with η hη hhη huη hwη
    rw [hη, hhη, huη, hwη]
    change (etaBesselWeight s (0, η))⁻¹ • (etaBesselWeight s (0, η) • u (z, η)) = _
    rw [smul_smul, inv_mul_cancel₀ (etaWeight_ne_zero s η), one_smul]
  have hparameter :
      L.compLp (iteratedParameterFourier n (carrierFubiniEquiv n h)) =
        iteratedParameterFourier n (carrierFubiniEquiv n u) := by
    exact (iteratedParameterFourier_compLp L _).symm.trans
      (congrArg (iteratedParameterFourier n) hinput)
  have hm : Measurable (fun ξ : CarrierVariable n =>
      initialWeight s ((0 : CarrierParameter), ξ.2) •
        initialFourier n (partialUnitaryInverse n u) ξ) :=
    ((measurable_initialWeight s).comp (measurable_const.prodMk measurable_snd)).smul
      (Lp.stronglyMeasurable _).measurable
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun hm
    (Lp.stronglyMeasurable _).measurable)).mpr
  filter_upwards [initialFourier_partialUnitaryInverse_coeFn u,
    initialFourier_partialUnitaryInverse_coeFn h,
    L.coeFn_compLp (iteratedParameterFourier n (carrierFubiniEquiv n h))]
    with z huz hhz hLz
  have hz :
      (iteratedParameterFourier n (carrierFubiniEquiv n u)) z =ᵐ[volume]
        fun η => (etaBesselWeight s ((0 : CarrierParameter), η))⁻¹ •
          (iteratedParameterFourier n (carrierFubiniEquiv n h)) z η := by
    have heq := (congrArg (fun t : IteratedCarrierL2 n => t z) hparameter).symm.trans hLz
    filter_upwards [reciprocalWeightOperator_coeFn s
      ((iteratedParameterFourier n (carrierFubiniEquiv n h)) z)] with η hη
    exact (congrArg (fun t : TransverseL2 n => t η) heq).trans hη
  have hzscale := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (Euclidean (n - 1)))
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae hz
  filter_upwards [huz, hhz, hzscale] with ξ huξ hhξ hξ
  rw [huξ, hhξ, hξ, transverseWeight_rescale]
  rw [smul_comm (synthesisFactor n), smul_smul,
    mul_inv_cancel₀ (etaWeight_ne_zero s _)]
  simp

/-- Exact transverse weighted Plancherel on compact smooth tests, supplying
both membership and norm equality for `app:ch_background:prop:bg-adjoint`.
The reciprocal-weight argument uses only the actual partial Fourier operators;
compact support supplies the weighted input integrability. -/
theorem transverseInitialFourier_test_memLp_norm (s : ℕ) (f : carrierInitialTestSpace n) :
    MemLp (fun ξ : CarrierVariable n => initialWeight s ((0 : CarrierParameter), ξ.2) •
      initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ∧
    lpNorm (fun ξ : CarrierVariable n => initialWeight s ((0 : CarrierParameter), ξ.2) •
      initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) = lpNorm (weightedCarrierJet 0 s f.val) 2 (carrierMeasure n) := by
  have hj := memLp_weightedCarrierJet_of_compactSupport 0 s f.property.1 f.property.2
  have hw : MemLp (fun x => etaBesselWeight s x • f.val x) 2 (carrierMeasure n) :=
    hj.congr_norm ((continuous_etaBesselWeight s).smul f.property.1.continuous).aestronglyMeasurable
      (Eventually.of_forall (norm_weightedCarrierJet_zero s f.val))
  let h : CarrierL2 n := hw.toLp _
  have hh : h =ᵐ[carrierMeasure n]
      fun x => etaBesselWeight s x • carrierInitialTestToLp f x := by
    filter_upwards [hw.coeFn_toLp, (carrierInitialTest_memLp f).coeFn_toLp] with x hx hf
    exact hx.trans (congrArg (fun a : ℂ => etaBesselWeight s x • a) hf.symm)
  have he := weighted_fourier_synthesis_coeFn s (carrierInitialTestToLp f) h hh
  have hmem : MemLp (⇑(initialFourier n (partialUnitaryInverse n h))) 2 (carrierMeasure n) :=
    Lp.memLp _
  refine ⟨hmem.ae_eq he.symm, ?_⟩
  calc
    _ = ‖initialFourier n (partialUnitaryInverse n h)‖ :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae he)
    _ = ‖h‖ := by rw [initialFourier_norm, partialUnitaryInverse_norm]
    _ = lpNorm (fun x => etaBesselWeight s x • f.val x) 2 (carrierMeasure n) :=
      Lp.norm_toLp _ hw
    _ = _ := by
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_norm_ae hw.aestronglyMeasurable hj.aestronglyMeasurable
      exact Eventually.of_forall fun x => (norm_weightedCarrierJet_zero s f.val x).symm

/-- The transverse input `hη` of
`partialUnitaryInverse_test_sobolev_bound_of_split_estimates`, with constant one
and no integrability or Plancherel premise. This is the η-weight part of
`app:ch_background:eq:bg-density-adjoint`. -/
theorem transverseInitialFourier_test_bound (s : ℕ) (f : carrierInitialTestSpace n) :
    MemLp (fun ξ : CarrierVariable n => initialWeight s ((0 : CarrierParameter), ξ.2) •
      initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ∧
    lpNorm (fun ξ : CarrierVariable n => initialWeight s ((0 : CarrierParameter), ξ.2) •
      initialFourier n (partialUnitaryInverse n (carrierInitialTestToLp f)) ξ)
        2 (carrierMeasure n) ≤ lpNorm (weightedCarrierJet 0 s f.val) 2 (carrierMeasure n) := by
  obtain ⟨hm, hn⟩ := transverseInitialFourier_test_memLp_norm s f
  exact ⟨hm, hn.le⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
