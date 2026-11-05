module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Coordinates

/-!
# Full product L² dilation

The unitary normalization of `app:ch_waves:eq:sampling-prefix-normal` on the
literal product measure. The scalar is the square root of the transverse
Jacobian, including the bottom band.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase

section Pullback
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) {J : ℝ}
  (hJ : 0 < J) (he : μ.map e = ENNReal.ofReal J⁻¹ • ν)

include he in
/-- Square integrability for the full-input Jacobian pullback
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weightedPullback_memLp (f : Lp ℂ 2 ν) :
    MemLp (fun x ↦ (Real.sqrt J : ℂ) * f (e x)) 2 μ := by
  apply MemLp.const_mul
  apply MemLp.comp_of_map _ e.measurable.aemeasurable
  rw [he]
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

/-- Auxiliary weighted pullback used only to construct `fullBandDilation`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def weightedPullback (f : Lp ℂ 2 ν) : Lp ℂ 2 μ :=
  (weightedPullback_memLp e he f).toLp _

/-- Auxiliary identity for the unitary full-input normalization in
`app:ch_waves:eq:sampling-prefix-normal`, consumed by `fullBandDilation`. -/
theorem weightedPullback_ae (f : Lp ℂ 2 ν) :
    weightedPullback e he f =ᵐ[μ] fun x ↦ (Real.sqrt J : ℂ) * f (e x) :=
  MemLp.coeFn_toLp _

include he in
/-- Auxiliary identity for the unitary full-input normalization in
`app:ch_waves:eq:sampling-prefix-normal`, consumed by `fullBandDilation`. -/
theorem ae_weightedPullback {p : Y → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ x ∂μ, p (e x) := by
  apply ae_of_ae_map e.measurable.aemeasurable
  rw [he]
  exact Measure.ae_smul_measure hp _

/-- Linearity of the full-input Jacobian pullback
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def weightedPullbackLinear : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := weightedPullback e he
  map_add' f g := by
    apply Lp.ext
    filter_upwards [weightedPullback_ae e he (f + g), weightedPullback_ae e he f,
      weightedPullback_ae e he g, Lp.coeFn_add (weightedPullback e he f)
        (weightedPullback e he g), ae_weightedPullback e he (Lp.coeFn_add f g)]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₄, Pi.add_apply, h₂, h₃, h₅, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [weightedPullback_ae e he (c • f), weightedPullback_ae e he f,
      Lp.coeFn_smul c (weightedPullback e he f),
      ae_weightedPullback e he (Lp.coeFn_smul c f)] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₃, Pi.smul_apply, h₂, h₄, smul_eq_mul, RingHom.id_apply]
    ring

include hJ in
/-- Auxiliary identity for the unitary full-input normalization in
`app:ch_waves:eq:sampling-prefix-normal`, consumed by `fullBandDilation`. -/
theorem weightedPullback_norm (f : Lp ℂ 2 ν) :
    ‖weightedPullback e he f‖ = ‖f‖ := by
  have hsq : ‖weightedPullback e he f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ),
      l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
    calc
      _ = ∫ x, J * ‖f (e x)‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [weightedPullback_ae e he f] with x hx
        rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hJ.le]
      _ = _ := by
        rw [integral_const_mul, ← integral_map_equiv e (fun y ↦ ‖f y‖ ^ 2), he, integral_smul_measure,
          ENNReal.toReal_ofReal (inv_nonneg.mpr hJ.le), smul_eq_mul,
          ← mul_assoc, mul_inv_cancel₀ hJ.ne', one_mul]
  nlinarith [norm_nonneg (weightedPullback e he f), norm_nonneg f]

include hJ he in
/-- Auxiliary identity for the unitary full-input normalization in
`app:ch_waves:eq:sampling-prefix-normal`, consumed by `fullBandDilation`. -/
theorem map_inverse_weightedPullback :
    ν.map e.symm = ENNReal.ofReal (J⁻¹)⁻¹ • μ := by
  have h := congrArg (Measure.map e.symm) he
  rw [MeasurableEquiv.map_symm_map, Measure.map_smul _ e.symm.measurable.aemeasurable] at h
  calc
    _ = ENNReal.ofReal J • (ENNReal.ofReal J⁻¹ • ν.map e.symm) := by
      rw [smul_smul, ← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne',
        ENNReal.ofReal_one, one_smul]
    _ = _ := by rw [← h, inv_inv]

/-- Auxiliary identity for the unitary full-input normalization in
`app:ch_waves:eq:sampling-prefix-normal`, consumed by `fullBandDilation`. -/
theorem weightedPullback_inverse (f : Lp ℂ 2 ν) :
    weightedPullback e.symm (map_inverse_weightedPullback e hJ he)
      (weightedPullback e he f) = f := by
  apply Lp.ext
  filter_upwards [weightedPullback_ae e.symm (map_inverse_weightedPullback e hJ he)
    (weightedPullback e he f), ae_weightedPullback e.symm
      (map_inverse_weightedPullback e hJ he) (weightedPullback_ae e he f)] with y h₁ h₂
  rw [h₁, h₂, e.apply_symm_apply, Real.sqrt_inv, Complex.ofReal_inv,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Real.sqrt_pos.mpr hJ).ne'

/-- The Jacobian-weighted equivalence used by `fullBandDilation`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def weightedPullbackEquiv : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { weightedPullbackLinear e he with
      invFun := weightedPullback e.symm (map_inverse_weightedPullback e hJ he)
      left_inv := weightedPullback_inverse e hJ he
      right_inv := fun f ↦ by
        change weightedPullback e he _ = f
        simpa only [MeasurableEquiv.symm_symm, inv_inv] using
          weightedPullback_inverse e.symm (inv_pos.mpr hJ)
            (map_inverse_weightedPullback e hJ he) f }
  norm_map' := weightedPullback_norm e hJ he
end Pullback

/-- The unitary full-band input dilation, with the slice variable fixed and
factor `sqrt ((2^j)^(n-1))` (`app:ch_waves:eq:sampling-prefix-normal`). -/
def fullBandDilation (n j : ℕ) (B : ℝ) :
    FullBandInput n j B ≃ₗᵢ[ℂ] FullBandInput n 0 B := by
  exact weightedPullbackEquiv (fullInputDilation n j) (by positivity)
    (map_fullBandMeasure_dilation n j B)

/-- Literal representative of the full unitary input normalization
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullBandDilation_apply_ae (n j : ℕ) (B : ℝ) (f : FullBandInput n j B) :
    fullBandDilation n j B f =ᵐ[fullBandMeasure n 0 B] fun u ↦
      (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) * f (u.1, (2 : ℝ) ^ j • u.2) :=
  weightedPullback_ae (fullInputDilation n j) (map_fullBandMeasure_dilation n j B) f

/-- Both quadratures and the exact full input norm survive normalization
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem norm_fullBandDilation (n j : ℕ) (B : ℝ) (f : FullBandInput n j B) :
    ‖fullBandDilation n j B f‖ = ‖f‖ := (fullBandDilation n j B).norm_map f

/-- The inverse full-input normalization has the reciprocal square-root
Jacobian (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullBandDilation_symm_apply_ae (n j : ℕ) (B : ℝ) (f : FullBandInput n 0 B) :
    (fullBandDilation n j B).symm f =ᵐ[fullBandMeasure n j B] fun u ↦
      (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ)⁻¹ *
        f (u.1, ((2 : ℝ) ^ j)⁻¹ • u.2) := by
  change weightedPullback (fullInputDilation n j).symm
    (map_inverse_weightedPullback (fullInputDilation n j) (by positivity)
      (map_fullBandMeasure_dilation n j B)) f =ᵐ[_] _
  filter_upwards [weightedPullback_ae (fullInputDilation n j).symm
    (map_inverse_weightedPullback (fullInputDilation n j) (by positivity)
      (map_fullBandMeasure_dilation n j B)) f] with u hu
  rw [hu, Real.sqrt_inv, Complex.ofReal_inv]
  congr 2

/-- Euclidean coordinate transport on the actual restricted full input,
used after dilation in `app:ch_waves:eq:sampling-prefix-normal`. -/
def fullInputL2Coordinates (m j : ℕ) (B : ℝ) :
    FullBandInput (m + 1) j B ≃ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (fullInputDomain m j B)) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (fullInputCoordinates m).symm
    (fullInputCoordinates_restrict_measurePreserving m j B).symm
  invFun := Lp.compMeasurePreserving (fullInputCoordinates m)
    (fullInputCoordinates_restrict_measurePreserving m j B)
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply f

/-- The full restricted coordinate change is literally composition with the
inverse coordinate map (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullInputL2Coordinates_apply_ae (m j : ℕ) (B : ℝ)
    (f : FullBandInput (m + 1) j B) :
    fullInputL2Coordinates m j B f =ᵐ[volume.restrict (fullInputDomain m j B)]
      f ∘ (fullInputCoordinates m).symm :=
  Lp.coeFn_compMeasurePreserving _ _

end JanetCartan.Sampling.MeanNormalBound.NormalizedFullPhase
