module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Measure

/-!
# The unitary change of raw annular input

The actual complex `L²` dilation used just before
`app:ch_waves:eq:sampling-prefix-normal`. Its inverse and norm preservation use
restricted Lebesgue measure, rather than identifying this input with torus data.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization
variable {n : ℕ} {K R S : ℝ}

/-- The Jacobian-weighted pullback is square integrable, as required for the
input dilation in `app:ch_waves:thm:sampling`. -/
theorem annularPullback_memLp (hK : 0 < K) (hS : S = K * R) (f : AnnularL2 n S) :
    MemLp (fun θ ↦ (Real.sqrt (K ^ (n - 1)) : ℂ) * f (K • θ)) 2
      (annularMeasure n R) := by
  apply MemLp.const_mul
  apply MemLp.comp_of_map _ (by fun_prop)
  rw [map_annularMeasure_smul hK R, ← hS]
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

/-- The Jacobian-weighted pullback on `L²` classes, used to construct the
dilation and its inverse in `app:ch_waves:thm:sampling`. -/
def annularPullback (hK : 0 < K) (hS : S = K * R) (f : AnnularL2 n S) :
    AnnularL2 n R := (annularPullback_memLp hK hS f).toLp _

private theorem pullback_ae (hK : 0 < K) (hS : S = K * R) (f : AnnularL2 n S) :
    annularPullback hK hS f =ᵐ[annularMeasure n R]
      fun θ ↦ (Real.sqrt (K ^ (n - 1)) : ℂ) * f (K • θ) :=
  MemLp.coeFn_toLp _

private theorem ae_pullback (hK : 0 < K) (hS : S = K * R)
    {p : Euclidean (n - 1) → Prop} (hp : ∀ᵐ η ∂annularMeasure n S, p η) :
    ∀ᵐ θ ∂annularMeasure n R, p (K • θ) :=
  ae_annular_smul hK R (hS ▸ hp)

private theorem annular_norm_sq (f : AnnularL2 n R) :
    ‖f‖ ^ 2 = ∫ η, ‖f η‖ ^ 2 ∂annularMeasure n R := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Restricted Lebesgue change of variables preserves the pullback norm
(`app:ch_waves:thm:sampling`). -/
theorem annularPullback_norm (hK : 0 < K) (hS : S = K * R) (f : AnnularL2 n S) :
    ‖annularPullback hK hS f‖ = ‖f‖ := by
  have hsq : ‖annularPullback hK hS f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [annular_norm_sq, annular_norm_sq]
    calc
      _ = ∫ θ, K ^ (n - 1) * ‖f (K • θ)‖ ^ 2 ∂annularMeasure n R := by
        apply integral_congr_ae
        filter_upwards [pullback_ae hK hS f] with θ hθ
        rw [hθ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
      _ = _ := by
        rw [integral_const_mul, integral_annular_smul hK R (fun η ↦ ‖f η‖ ^ 2), ← hS, smul_eq_mul,
          ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hK _)), one_mul]
  nlinarith [norm_nonneg (annularPullback hK hS f), norm_nonneg f]

/-- Complex linearity of the weighted annular pullback
(`app:ch_waves:thm:sampling`). -/
def annularPullbackLinear (hK : 0 < K) (hS : S = K * R) :
    AnnularL2 n S →ₗ[ℂ] AnnularL2 n R where
  toFun := annularPullback hK hS
  map_add' f g := by
    apply Lp.ext
    filter_upwards [pullback_ae hK hS (f + g), pullback_ae hK hS f,
      pullback_ae hK hS g, Lp.coeFn_add (annularPullback hK hS f) (annularPullback hK hS g),
      ae_pullback hK hS (Lp.coeFn_add f g)] with θ h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₄, Pi.add_apply, h₂, h₃, h₅, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [pullback_ae hK hS (c • f), pullback_ae hK hS f,
      Lp.coeFn_smul c (annularPullback hK hS f), ae_pullback hK hS (Lp.coeFn_smul c f)]
      with θ h₁ h₂ h₃ h₄
    simp only [h₁, h₃, Pi.smul_apply, h₂, h₄, smul_eq_mul, RingHom.id_apply]
    ring

/-- Reciprocal dilations cancel on actual `L²` classes
(`app:ch_waves:thm:sampling`). -/
theorem annularPullback_inverse (hK : 0 < K) (hS : S = K * R)
    (hR : R = K⁻¹ * S) (f : AnnularL2 n S) :
    annularPullback (inv_pos.mpr hK) hR (annularPullback hK hS f) = f := by
  apply Lp.ext
  filter_upwards [pullback_ae (inv_pos.mpr hK) hR (annularPullback hK hS f),
    ae_pullback (inv_pos.mpr hK) hR (pullback_ae hK hS f)] with η h₁ h₂
  rw [h₁, h₂]
  simp only [smul_inv_smul₀ hK.ne', inv_pow, Real.sqrt_inv, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Real.sqrt_pos.mpr (pow_pos hK (n - 1))).ne'

/-- The actual unitary input dilation of `app:ch_waves:thm:sampling`.
It sends `f(η)` to `K^((n-1)/2) f(Kθ)` almost everywhere; both spaces use
literal restricted Lebesgue measure. -/
def annularDilation (n : ℕ) (K : ℝ) (hK : 0 < K) :
    AnnularL2 n K ≃ₗᵢ[ℂ] AnnularL2 n 1 where
  toLinearEquiv :=
    { annularPullbackLinear hK (mul_one K).symm with
      invFun := annularPullback (inv_pos.mpr hK) (inv_mul_cancel₀ hK.ne').symm
      left_inv := annularPullback_inverse hK (mul_one K).symm (inv_mul_cancel₀ hK.ne').symm
      right_inv := by
        intro g
        change annularPullback hK (mul_one K).symm _ = g
        simpa only [inv_inv] using
          annularPullback_inverse (inv_pos.mpr hK) (inv_mul_cancel₀ hK.ne').symm
            (by simp) g }
  norm_map' := annularPullback_norm hK (mul_one K).symm

/-- Almost-everywhere formula for the dilation in `app:ch_waves:thm:sampling`. -/
theorem annularDilation_apply_ae (hK : 0 < K) (f : AnnularL2 n K) :
    annularDilation n K hK f =ᵐ[annularMeasure n 1]
      fun θ ↦ (Real.sqrt (K ^ (n - 1)) : ℂ) * f (K • θ) :=
  pullback_ae hK (mul_one K).symm f

/-- Explicit inverse of the raw input dilation (`app:ch_waves:thm:sampling`). -/
theorem annularDilation_symm_apply_ae (hK : 0 < K) (g : AnnularL2 n 1) :
    (annularDilation n K hK).symm g =ᵐ[annularMeasure n K]
      fun η ↦ (Real.sqrt (K ^ (n - 1)) : ℂ)⁻¹ * g (K⁻¹ • η) := by
  change annularPullback (inv_pos.mpr hK) (inv_mul_cancel₀ hK.ne').symm g =ᵐ[_] _
  simpa only [inv_pow, Real.sqrt_inv, Complex.ofReal_inv] using
    pullback_ae (inv_pos.mpr hK) (inv_mul_cancel₀ hK.ne').symm g

/-- The square-root Jacobian has the manuscript exponent when `n ≥ 1`
(`app:ch_waves:thm:sampling`). -/
theorem sqrt_jacobian_eq_rpow (hn : 1 ≤ n) (hK : 0 < K) :
    Real.sqrt (K ^ (n - 1)) = K ^ (((n : ℝ) - 1) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast K (n - 1), ← Real.rpow_mul hK.le]
  congr 1
  rw [Nat.cast_sub hn]
  push_cast
  ring

/-- The forward formula with the manuscript's real-power exponent
(`app:ch_waves:thm:sampling`). -/
theorem annularDilation_apply_ae_rpow (hn : 1 ≤ n) (hK : 0 < K)
    (f : AnnularL2 n K) :
    annularDilation n K hK f =ᵐ[annularMeasure n 1]
      fun θ ↦ (K ^ (((n : ℝ) - 1) / 2) : ℝ) * f (K • θ) := by
  simpa only [sqrt_jacobian_eq_rpow hn hK] using annularDilation_apply_ae hK f

/-- The inverse formula with the manuscript's real-power exponent
(`app:ch_waves:thm:sampling`). -/
theorem annularDilation_symm_apply_ae_rpow (hn : 1 ≤ n) (hK : 0 < K)
    (g : AnnularL2 n 1) :
    (annularDilation n K hK).symm g =ᵐ[annularMeasure n K]
      fun η ↦ (K ^ (-((n : ℝ) - 1) / 2) : ℝ) * g (K⁻¹ • η) := by
  simpa only [sqrt_jacobian_eq_rpow hn hK, neg_div, Real.rpow_neg hK.le,
    Complex.ofReal_inv] using annularDilation_symm_apply_ae hK g

end JanetCartan.RawInputDilation
