module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic

/-!
# Negative Sobolev norms in physical and unit-period frequencies

The original-source estimate before `app:ch_response:eq:response-graded-reduced`
in `app:ch_response:prop:response-graded` uses physical frequency. The consumer
`modulatedSource_negative_sobolev` needs the actual Hilbert-valued L² Fourier
representative. The change of variables `ξ = 2π η` and comparison of negative
weights give the factor `(2π)^(M - n/2)`.

The ordinary Fourier integral is identified with the L² transform by the proved
Hilbert-valued identification in `Localization.PhysicalPlancherel`. Membership
and integrability are proved before taking real-valued norms and integrals.
No phase, envelope, or source-shell estimate is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.ResponseTransfer.SourceNegative

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The weight comparison used by `negative_fourier_norm_le_physical`, for the
original-source estimate in `app:ch_response:prop:response-graded`. -/
private theorem negative_weight_dilation {a M : ℝ} (ha : 1 ≤ a) (hM : 0 ≤ M)
    (η : Euclidean n) :
    (1 + ‖η‖ ^ 2) ^ (-M) ≤
      a ^ (2 * M) * (1 + ‖a • η‖ ^ 2) ^ (-M) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb : 1 + ‖a • η‖ ^ 2 ≤ a ^ 2 * (1 + ‖η‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
    nlinarith [sq_nonneg (a - 1)]
  have hw := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + ‖a • η‖ ^ 2)
    hb (neg_nonpos.mpr hM)
  calc
    _ = a ^ (2 * M) * (a ^ 2 * (1 + ‖η‖ ^ 2)) ^ (-M) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
        ← Real.rpow_natCast a 2, ← Real.rpow_mul ha0.le, ← Real.rpow_add ha0]
      ring_nf
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

/-- The actual Hilbert-valued Fourier representative belongs to every negative
Sobolev order. This supplies the membership accompanying the numerical bound
in `negative_fourier_norm_le_physical` (`app:ch_response:prop:response-graded`). -/
theorem negative_weighted_fourier_memLp (u : Lp (α := Euclidean n) F 2 volume)
    {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun η ↦ Pseudodifferential.euclideanSobolevWeight (-M) η •
      (𝓕 u : Lp (α := Euclidean n) F 2 volume) η) 2 volume := by
  apply (Lp.memLp (𝓕 u)).mono
    ((Pseudodifferential.continuous_euclideanSobolevWeight (-M)).aestronglyMeasurable.smul
      (Lp.memLp _).aestronglyMeasurable)
  filter_upwards [] with η
  change ‖Pseudodifferential.euclideanSobolevWeight (-M) η • (𝓕 u) η‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Pseudodifferential.euclideanSobolevWeight_pos (-M) η)]
  have hw : Pseudodifferential.euclideanSobolevWeight (-M) η ≤ 1 := by
    simpa using Pseudodifferential.euclideanSobolevWeight_mono (neg_nonpos.mpr hM) η
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans_eq (one_mul _)

omit [CompleteSpace F] in
private theorem norm_sq_weighted (M : ℝ) (H : Euclidean n → F) (η : Euclidean n) :
    ‖Pseudodifferential.euclideanSobolevWeight (-M) η • H η‖ ^ 2 =
      (1 + ‖η‖ ^ 2) ^ (-M) * ‖H η‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Pseudodifferential.euclideanSobolevWeight_pos (-M) η), mul_pow]
  congr 1
  rw [Pseudodifferential.euclideanSobolevWeight, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  congr 1
  norm_num

omit [CompleteSpace F] [InnerProductSpace ℂ F] in
private theorem eLpNorm_two_toReal_eq_sqrt {g : Euclidean n → F} (hg : MemLp g 2 volume) :
    (eLpNorm g 2 volume).toReal = Real.sqrt (∫ η, ‖g η‖ ^ 2) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num

/-- The physical-frequency negative Sobolev energy is integrable for an L¹ ∩ L²
source. This justifies the right-hand norm in `negative_fourier_norm_le_physical`
(`app:ch_response:prop:response-graded`). -/
theorem integrable_negative_physicalFourier_energy {h : Euclidean n → F}
    (hh : Integrable h volume) (h₂ : MemLp h 2 volume) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-M) *
      ‖Localization.physicalFourierIntegral volume h
        (InnerProductSpace.toDual ℝ (Euclidean n) ξ)‖ ^ 2) volume := by
  have hi := Localization.integrable_norm_sq_physicalFourierIntegral hh
    ((memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂)
  apply hi.bdd_mul (c := 1)
  · apply Continuous.aestronglyMeasurable
    exact Continuous.rpow_const (by fun_prop) (fun ξ ↦ Or.inl (by positivity))
  · filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])
      (neg_nonpos.mpr hM)

/-- Compare the actual weighted L² Fourier norm with the physical-frequency
norm, with the explicit factor `(2π)^(M - n/2)`. This is the normalization step
for `modulatedSource_negative_sobolev`, the original-source estimate immediately
before `app:ch_response:eq:response-graded-reduced`. -/
theorem negative_fourier_norm_le_physical {h : Euclidean n → F}
    (hh : Integrable h volume) (h₂ : MemLp h 2 volume) {M : ℝ} (hM : 0 ≤ M) :
    (eLpNorm (fun η ↦ Pseudodifferential.euclideanSobolevWeight (-M) η •
      (𝓕 (h₂.toLp h) : Lp (α := Euclidean n) F 2 volume) η) 2 volume).toReal ≤
      (2 * Real.pi) ^ (M - (n : ℝ) / 2) *
        Localization.fourierWeightedL2Norm volume (-M) (fun ξ ↦
          Localization.physicalFourierIntegral volume h
            (InnerProductSpace.toDual ℝ (Euclidean n) ξ)) := by
  let a : ℝ := 2 * Real.pi
  have ha : 1 ≤ a := by dsimp [a]; linarith [Real.two_le_pi]
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let H : Euclidean n → F := fun ξ ↦ Localization.physicalFourierIntegral volume h
    (InnerProductSpace.toDual ℝ (Euclidean n) ξ)
  let energy : Euclidean n → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-M) * ‖H ξ‖ ^ 2
  have hi : Integrable energy volume := integrable_negative_physicalFourier_energy hh h₂ hM
  have hf : Integrable (h₂.toLp h : Euclidean n → F) := hh.congr h₂.coeFn_toLp.symm
  have he : (𝓕 (h₂.toLp h) : Lp (α := Euclidean n) F 2 volume) =ᵐ[volume] 𝓕 h :=
    (Localization.fourierTransform_coeFn_ae_integral_hilbert (h₂.toLp h) hf).trans
      (Filter.Eventually.of_forall (Real.fourier_congr_ae h₂.coeFn_toLp))
  have hH (η : Euclidean n) : H (a • η) = 𝓕 h η := by
    dsimp [H]
    rw [Localization.physicalFourierIntegral_eq_fourier]
    change 𝓕 h (a⁻¹ • a • η) = _
    rw [inv_smul_smul₀ ha0.ne']
  have hm := negative_weighted_fourier_memLp (h₂.toLp h) hM
  have hiw := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hiw' : Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ (-M) * ‖𝓕 h η‖ ^ 2) volume := by
    apply hiw.congr
    filter_upwards [he] with η hη
    rw [norm_sq_weighted, hη]
  have hcomp : (∫ η, energy (a • η)) = (a ^ n)⁻¹ * ∫ ξ, energy ξ := by
    simpa only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
      Measure.integral_comp_smul_of_nonneg volume energy a (hR := ha0.le)
  have hib : (∫ η, (1 + ‖η‖ ^ 2) ^ (-M) * ‖𝓕 h η‖ ^ 2) ≤
      a ^ (2 * M) * (a ^ n)⁻¹ * ∫ ξ, energy ξ := by
    rw [mul_assoc, ← hcomp, ← integral_const_mul]
    apply integral_mono hiw' ((hi.comp_smul ha0.ne').const_mul _)
    intro η
    dsimp [energy]
    rw [hH, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (negative_weight_dilation ha hM η) (sq_nonneg _)
  have hc : a ^ (2 * M) * (a ^ n)⁻¹ = a ^ (2 * (M - (n : ℝ) / 2)) := by
    rw [← Real.rpow_natCast a n, ← Real.rpow_neg ha0.le, ← Real.rpow_add ha0]
    congr 1
    ring
  rw [eLpNorm_two_toReal_eq_sqrt hm]
  have heI : (∫ η, ‖Pseudodifferential.euclideanSobolevWeight (-M) η •
      (𝓕 (h₂.toLp h) : Lp (α := Euclidean n) F 2 volume) η‖ ^ 2) =
      ∫ η, (1 + ‖η‖ ^ 2) ^ (-M) * ‖𝓕 h η‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [he] with η hη
    rw [norm_sq_weighted, hη]
  rw [heI]
  apply (Real.sqrt_le_sqrt hib).trans_eq
  rw [hc, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_mul ha0.le]
  change a ^ (2 * (M - (n : ℝ) / 2) * (1 / 2)) * Real.sqrt (∫ ξ, energy ξ) =
    a ^ (M - (n : ℝ) / 2) * Real.sqrt (∫ ξ, energy ξ)
  congr 2
  ring

/-- Scalar specialization of `negative_fourier_norm_le_physical` in the existing
Sobolev API, for the original-source estimate in
`app:ch_response:prop:response-graded`. Its membership is supplied by
`Pseudodifferential.memFourierSobolev_of_nonpos (neg_nonpos.mpr hM)`. -/
theorem fourierSobolevNorm_negative_le_physical {h : Euclidean n → ℂ}
    (hh : Integrable h volume) (h₂ : MemLp h 2 volume) {M : ℝ} (hM : 0 ≤ M) :
    Pseudodifferential.fourierSobolevNorm (-M) (h₂.toLp h) ≤
      (2 * Real.pi) ^ (M - (n : ℝ) / 2) *
        Localization.fourierWeightedL2Norm volume (-M) (fun ξ ↦
          Localization.physicalFourierIntegral volume h
            (InnerProductSpace.toDual ℝ (Euclidean n) ξ)) :=
  negative_fourier_norm_le_physical hh h₂ hM

end JanetCartan.ResponseTransfer.SourceNegative
