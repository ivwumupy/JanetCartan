module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Normalization
/-!
# The unitary radian inverse transform on transverse L²

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
the partial transform leaves the carrier parameter fixed. This leaf constructs
its transverse operator, with an explicit dilation inverse and the exact
`synthesisFactor n` normalization. The product-space assembly consumes this
operator after the L² Fubini identification. No positive-dimension assumption
is needed. The codomain can be any complete complex Hilbert space.
-/

open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace ContDiff
@[expose] public noncomputable section
namespace JanetCartan.CarrierSobolev
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
private theorem memLp_transverse_scale (f : Lp F 2 (volume : Measure (Euclidean (n - 1))))
    (a b : ℝ) (ha : a ≠ 0) :
    MemLp (fun x => b • f (a • x)) 2 volume := by
  have hm := (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume ha)
  apply (memLp_two_iff_integrable_sq_norm (hm.const_smul b)).mpr
  change Integrable (fun x => ‖b • f (a • x)‖ ^ 2)
  simp only [norm_smul, mul_pow]
  exact ((Lp.memLp f).integrable_norm_pow (by decide)).comp_smul ha |>.const_mul _

omit [CompleteSpace F] in
private theorem integral_sq_norm (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- Rescaling a transverse L² representative by a nonzero coordinate factor
and a scalar amplitude. The two choices in `transverseDilation` implement its
forward and inverse maps (`app:ch_background:prop:bg-adjoint`). -/
def transverseScale (a b : ℝ) (ha : a ≠ 0)
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) : Lp F 2 (volume : Measure (Euclidean (n - 1))) :=
  (show MemLp (fun x => b • f (a • x)) 2 volume from by
    exact memLp_transverse_scale f a b ha).toLp _

omit [CompleteSpace F] in
/-- Representative formula used to prove both inverse identities for
`transverseDilation` (`app:ch_background:prop:bg-inverse`). -/
theorem transverseScale_coeFn (a b : ℝ) (ha : a ≠ 0)
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    transverseScale a b ha f =ᵐ[volume] fun x => b • f (a • x) :=
  MemLp.coeFn_toLp _

/-- The unitary dilation converting unit-period inverse Fourier coordinates to
radian coordinates in `app:ch_background:prop:bg-adjoint`. Its inverse sends
`f(y)` to `synthesisFactor n • f ((2π) • y)`. -/
def transverseDilation (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] :
    Lp F 2 (volume : Measure (Euclidean (n - 1))) ≃ₗᵢ[ℂ]
      Lp F 2 (volume : Measure (Euclidean (n - 1))) where
  toFun := transverseScale (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹ (by positivity)
  invFun := transverseScale (2 * Real.pi) (synthesisFactor n) (by positivity)
  left_inv f := by
    apply Lp.ext
    have he := transverseScale_coeFn (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
      (by positivity) f
    have he' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae he
    filter_upwards [transverseScale_coeFn (2 * Real.pi) (synthesisFactor n)
      (by positivity) (transverseScale (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
        (by positivity) f), he'] with x hx hy
    rw [hx, hy]
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt (synthesisFactor_pos n)),
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  right_inv f := by
    apply Lp.ext
    have he := transverseScale_coeFn (2 * Real.pi) (synthesisFactor n) (by positivity) f
    have he' := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
      (by positivity : (2 * Real.pi : ℝ)⁻¹ ≠ 0)).ae he
    filter_upwards [transverseScale_coeFn (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
      (by positivity) (transverseScale (2 * Real.pi) (synthesisFactor n)
        (by positivity) f), he'] with x hx hy
    rw [hx, hy]
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt (synthesisFactor_pos n)),
      mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  map_add' f g := by
    let D := transverseScale (n := n) (F := F) (2 * Real.pi)⁻¹
      (synthesisFactor n)⁻¹ (by positivity)
    have hD := transverseScale_coeFn (n := n) (F := F) (2 * Real.pi)⁻¹
      (synthesisFactor n)⁻¹ (by positivity)
    change D (f + g) = D f + D g
    apply Lp.ext
    have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
      (by positivity : (2 * Real.pi : ℝ)⁻¹ ≠ 0)).ae (Lp.coeFn_add f g)
    filter_upwards [hD (f + g), Lp.coeFn_add (D f) (D g), hD f, hD g, he]
      with x h1 h2 h3 h4 h5
    dsimp only [D] at h2 ⊢
    simp only [h1, h2, Pi.add_apply, h3, h4, h5, smul_add]
  map_smul' c f := by
    let D := transverseScale (n := n) (F := F) (2 * Real.pi)⁻¹
      (synthesisFactor n)⁻¹ (by positivity)
    have hD := transverseScale_coeFn (n := n) (F := F) (2 * Real.pi)⁻¹
      (synthesisFactor n)⁻¹ (by positivity)
    change D (c • f) = c • D f
    apply Lp.ext
    have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
      (by positivity : (2 * Real.pi : ℝ)⁻¹ ≠ 0)).ae (Lp.coeFn_smul c f)
    filter_upwards [hD (c • f), Lp.coeFn_smul c (D f), hD f, he] with x h1 h2 h3 h4
    dsimp only [D] at h2 ⊢
    simp only [h1, h2, Pi.smul_apply, h3, h4]
    exact smul_comm _ _ _
  norm_map' f := by
    change ‖transverseScale (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹ (by positivity) f‖ = ‖f‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← integral_sq_norm (transverseScale (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
      (by positivity) f), ← integral_sq_norm f]
    have he : (∫ x, ‖transverseScale (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
        (by positivity) f x‖ ^ 2) =
        ∫ x, ‖(synthesisFactor n)⁻¹ • f ((2 * Real.pi)⁻¹ • x)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [transverseScale_coeFn (2 * Real.pi)⁻¹ (synthesisFactor n)⁻¹
        (by positivity) f] with x hx
      rw [hx]
    rw [he]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (synthesisFactor_pos n)),
      mul_pow, integral_const_mul]
    rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖f x‖ ^ 2)
      (by positivity : 0 ≤ 2 * Real.pi)]
    simp only [smul_eq_mul, finrank_euclideanSpace, Fintype.card_fin]
    rw [← synthesisFactor_sq]
    field_simp [ne_of_gt (synthesisFactor_pos n)]


/-- Representative formula for the normalization dilation consumed by
`transverseUnitaryInverse_coeFn` (`app:ch_background:prop:bg-adjoint`). -/
theorem transverseDilation_coeFn (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    transverseDilation n F f =ᵐ[volume]
      fun y => (synthesisFactor n)⁻¹ • f ((2 * Real.pi)⁻¹ • y) :=
  transverseScale_coeFn _ _ (by positivity) f

/-- Hilbert-valued inverse integral identification for the transverse L²
operator in `app:ch_background:prop:bg-adjoint`. This also permits infinite
dimensional Hilbert fibers, unlike the finite-dimensional envelope API. -/
theorem transverseFourierInv_coeFn_ae_integral_hilbert (f : Lp F 2 (volume : Measure (Euclidean (n - 1))))
    (hf : Integrable (f : Euclidean (n - 1) → F)) :
    (𝓕⁻ f : Lp F 2 volume) =ᵐ[volume] 𝓕⁻ (f : Euclidean (n - 1) → F) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ f)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (-innerSL ℝ).continuous₂ hf).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution (Euclidean (n - 1)) F ↦ T s)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ) (μ := volume) (ν := volume)
    (L := -innerₗ (Euclidean (n - 1)))
    Real.continuous_fourierChar continuous_inner.neg s.integrable hf
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hd
  have hs' : (∫ x, (𝓕⁻ s) x • f x) = ∫ x, s x • 𝓕⁻ (f : Euclidean (n - 1) → F) x := by
    have hflip : (-innerₗ (Euclidean (n - 1))).flip = -innerₗ (Euclidean (n - 1)) := by
      ext x y
      simp [real_inner_comm]
    simpa [SchwartzMap.fourierInv_coe, hflip] using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

/-- Actual unitary radian inverse Fourier equivalence on the transverse L²
space (`app:ch_background:prop:bg-adjoint`; `app:ch_background:prop:bg-inverse`).
The iterated carrier operator applies this equivalence independently at each `z`. -/
def transverseUnitaryInverse (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] :
    Lp F 2 (volume : Measure (Euclidean (n - 1))) ≃ₗᵢ[ℂ]
      Lp F 2 (volume : Measure (Euclidean (n - 1))) :=
  (Lp.fourierTransformₗᵢ (Euclidean (n - 1)) F).symm.trans (transverseDilation n F)

/-- On integrable L² representatives, the equivalence is the ordinary unitary
inverse integral, including `(synthesisFactor n)⁻¹`
(`app:ch_background:prop:bg-adjoint`). -/
theorem transverseUnitaryInverse_coeFn (f : Lp F 2 (volume : Measure (Euclidean (n - 1))))
    (hf : Integrable (f : Euclidean (n - 1) → F)) :
    transverseUnitaryInverse n F f =ᵐ[volume]
      unitaryInverseIntegral (f : Euclidean (n - 1) → F) := by
  have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
    (by positivity : (2 * Real.pi : ℝ)⁻¹ ≠ 0)).ae (transverseFourierInv_coeFn_ae_integral_hilbert f hf)
  filter_upwards [transverseDilation_coeFn (𝓕⁻ f), he] with y hy he
  change transverseDilation n F (𝓕⁻ f) y = _
  rw [hy, he, unitaryInverseIntegral, radianInverseIntegral_eq_fourierInv]

/-- Representative formula for L¹ ∩ L² data, in particular compact smooth
transverse tests (`app:ch_background:prop:bg-adjoint`). -/
theorem transverseUnitaryInverse_toLp {f : Euclidean (n - 1) → F}
    (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    transverseUnitaryInverse n F (h₂.toLp f) =ᵐ[volume] unitaryInverseIntegral f := by
  refine (transverseUnitaryInverse_coeFn _ (h₁.congr h₂.coeFn_toLp.symm)).trans ?_
  exact Filter.Eventually.of_forall fun y => by
    simp only [unitaryInverseIntegral, radianInverseIntegral_eq_fourierInv]
    rw [Real.fourierInv_congr_ae h₂.coeFn_toLp]

/-- Transverse Plancherel for the initial Sobolev realization
(`app:ch_background:prop:bg-adjoint`). -/
theorem transverseUnitaryInverse_norm
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    ‖transverseUnitaryInverse n F f‖ = ‖f‖ :=
  (transverseUnitaryInverse n F).norm_map f

/-- Left inverse identity for the initial-variable realization
(`app:ch_background:prop:bg-inverse`). -/
theorem transverseUnitaryInverse_symm_apply_apply
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    (transverseUnitaryInverse n F).symm (transverseUnitaryInverse n F f) = f :=
  (transverseUnitaryInverse n F).symm_apply_apply f

/-- Right inverse identity for the initial-variable realization
(`app:ch_background:prop:bg-inverse`). -/
theorem transverseUnitaryInverse_apply_symm_apply
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    transverseUnitaryInverse n F ((transverseUnitaryInverse n F).symm f) = f :=
  (transverseUnitaryInverse n F).apply_symm_apply f

/-- Removing the explicit radian dilation recovers Mathlib's L² inverse
transform (`app:ch_background:prop:bg-adjoint`). -/
theorem transverseDilation_symm_unitaryInverse
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    (transverseDilation n F).symm (transverseUnitaryInverse n F f) = 𝓕⁻ f :=
  (transverseDilation n F).symm_apply_apply _

end JanetCartan.CarrierSobolev
