module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.EnergyBound.Identification

/-!
# Bounds for the literal frozen-model energy

This is the concrete energy adapter for the frozen step of
`app:ch_background:prop:bg-frame` (the Euclidean low-frequency argument in
`paper-v2.tex`). It transfers the proved `EuclideanSupportGap` estimates to
`euclideanFrozenEnergy`, retaining both Fourier quadratures and the physical
frequency `2πξ`. The loss is the explicit cycles-frequency ball volume
`c * volume (ball 0 (R₀ / (2π)))`.

The consuming construction `jc-frozen-continuum-model` must instantiate the
continuous bounded symbol and real high-frequency gap produced by
`jc-frozen-model-spectral`; positivity of its actual `frozenMatrixSymbol` is
already proved in `Symbol`. Its literal carrier-energy identity is produced
separately by `jc-frozen-model-fourier`. Any image-error allowance below must
come from the actual image comparison. These deductions prove bounds for the
frozen integral, and do not assert actual row coercivity.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open EuclideanSupportGap

variable {n : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => Lp (α := E) V 2 volume

/-- The frozen-model estimate of `app:ch_background:prop:bg-frame` for every
L¹ ∩ L² complex vector field. All constants and the physical spectral cutoff
are fixed before the field. Positivity and the high-frequency gap concern the
real matrix; the Fourier and integrability statements are proved consequences. -/
theorem euclideanFrozenEnergy_ge_sub_low_frequency
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {c M R₀ : ℝ} (hc : 0 ≤ c) (hM : ∀ k, ‖b k‖ ≤ M)
    (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : E,
      c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    (f : E → V) (hf : Integrable f) (hf₂ : MemLp f 2 volume) :
    c * (∫ x, ‖f x‖ ^ 2) - lowFrequencyConstant n c R₀ * (∫ x, ‖f x‖) ^ 2 ≤
      euclideanFrozenEnergy b f := by
  have hbound (k : E) : ‖complexifyMatrix (b k)‖ ≤ 2 * M :=
    (norm_complexifyMatrix_le_two_mul_frobenius (b k)).trans (by gcongr; exact hM k)
  have h := energy_ge_sub_low_frequency (fun k ↦ complexifyMatrix (b k))
    (continuous_complexifyMatrix hb) hc hbound
    (fun k z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_nonneg (hnonneg k) z)
    (fun k hk z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_ge (hgap k hk) z)
    (hf₂.toLp f) (hf.congr hf₂.coeFn_toLp.symm)
  rw [energy_complexifyMatrix_toLp_eq_euclideanFrozenEnergy b f hf hf₂,
    ← SingleChannel.integral_norm_sq_eq_toLp_norm_sq hf₂] at h
  have hL₁ : (∫ x, ‖(hf₂.toLp f) x‖) = ∫ x, ‖f x‖ :=
    integral_congr_ae (hf₂.coeFn_toLp.fun_comp norm)
  rwa [hL₁] at h

/-- The supported-L² frozen bound, including any fixed nonnegative
image-comparison allowance, in `app:ch_background:prop:bg-frame`.
L¹ membership follows from finite support; the support-volume loss follows
from the leaf's proved Cauchy–Schwarz estimate. -/
theorem euclideanFrozenEnergy_sub_integral_error_ge_support_volume
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {c M R₀ C_image : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C_image)
    (hM : ∀ k, ‖b k‖ ≤ M) (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : E,
      c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    (u : L²) (s : Set E) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (hsupp : ∀ᵐ x, x ∉ s → u x = 0) :
    (c - (lowFrequencyConstant n c R₀ + C_image) * (volume s).toReal) * ‖u‖ ^ 2 ≤
      euclideanFrozenEnergy b u - C_image * (∫ x, ‖u x‖) ^ 2 := by
  have hbound (k : E) : ‖complexifyMatrix (b k)‖ ≤ 2 * M :=
    (norm_complexifyMatrix_le_two_mul_frobenius (b k)).trans (by gcongr; exact hM k)
  have h := energy_sub_integral_error_ge_support_volume (fun k ↦ complexifyMatrix (b k))
    (continuous_complexifyMatrix hb) hc hC hbound
    (fun k z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_nonneg (hnonneg k) z)
    (fun k hk z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_ge (hgap k hk) z)
    u s hs hfinite hsupp
  rwa [energy_complexifyMatrix_eq_euclideanFrozenEnergy b u
    (integrable_of_supported u s hs hfinite hsupp)] at h

/-- The supported-L² estimate for the literal frozen energy, with no image
error, in `app:ch_background:prop:bg-frame`. -/
theorem euclideanFrozenEnergy_ge_support_volume
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {c M R₀ : ℝ} (hc : 0 ≤ c) (hM : ∀ k, ‖b k‖ ≤ M)
    (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : E,
      c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    (u : L²) (s : Set E) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (hsupp : ∀ᵐ x, x ∉ s → u x = 0) :
    (c - lowFrequencyConstant n c R₀ * (volume s).toReal) * ‖u‖ ^ 2 ≤
      euclideanFrozenEnergy b u := by
  simpa using euclideanFrozenEnergy_sub_integral_error_ge_support_volume b hb hc
    (C_image := 0) le_rfl hM hnonneg hgap u s hs hfinite hsupp

/-- The same finite-support bound for a specified L² function, in the
integral form consumed by the literal carrier identity
(`app:ch_background:prop:bg-frame`). Integrability is derived from support. -/
theorem euclideanFrozenEnergy_ge_support_volume_of_memLp
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {c M R₀ : ℝ} (hc : 0 ≤ c) (hM : ∀ k, ‖b k‖ ≤ M)
    (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : E,
      c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    (f : E → V) (hf₂ : MemLp f 2 volume)
    (s : Set E) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (hsupp : ∀ᵐ x, x ∉ s → f x = 0) :
    (c - lowFrequencyConstant n c R₀ * (volume s).toReal) * (∫ x, ‖f x‖ ^ 2) ≤
      euclideanFrozenEnergy b f := by
  have hsupp' : ∀ᵐ x, x ∉ s → (hf₂.toLp f) x = 0 := by
    filter_upwards [hsupp, hf₂.coeFn_toLp] with x hx heq hxs
    rw [heq, hx hxs]
  have hu := integrable_of_supported (hf₂.toLp f) s hs hfinite hsupp'
  have hf : Integrable f := hu.congr hf₂.coeFn_toLp
  have h := euclideanFrozenEnergy_ge_support_volume b hb hc hM hnonneg hgap
    (hf₂.toLp f) s hs hfinite hsupp'
  rw [← energy_complexifyMatrix_eq_euclideanFrozenEnergy b (hf₂.toLp f) hu,
    energy_complexifyMatrix_toLp_eq_euclideanFrozenEnergy b f hf hf₂,
    ← SingleChannel.integral_norm_sq_eq_toLp_norm_sq hf₂] at h
  exact h

/-- Choose the inner physical radius only after fixing the actual symbol,
spectral cutoff, image allowance and outer cap (`app:ch_background:prop:bg-frame`).
This transfers the leaf's radius choice to the literal frozen-model energy;
the actual operator identity and image comparison remain separate obligations. -/
theorem exists_inner_radius_euclideanFrozenEnergy_gap (hn : 0 < n)
    (b : E → Matrix (Fin n) (Fin n) ℝ) (hb : Continuous b)
    {c M R₀ C_image : ℝ} (hc : 0 < c) (hC : 0 ≤ C_image)
    (hM : ∀ k, ‖b k‖ ≤ M) (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : E,
      c * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    {r_outer : ℝ} (houter : 0 < r_outer) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r_outer ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : L²,
        (∀ᵐ x, x ∉ Metric.ball (0 : E) r → u x = 0) →
        c / 2 * ‖u‖ ^ 2 ≤ euclideanFrozenEnergy b u - C_image * (∫ x, ‖u x‖) ^ 2 := by
  have hbound (k : E) : ‖complexifyMatrix (b k)‖ ≤ 2 * M :=
    (norm_complexifyMatrix_le_two_mul_frobenius (b k)).trans (by gcongr; exact hM k)
  obtain ⟨r₀, hr₀, hcap, h⟩ := exists_inner_radius_gap hn (fun k ↦ complexifyMatrix (b k))
    (continuous_complexifyMatrix hb) hc hC hbound
    (fun k z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_nonneg (hnonneg k) z)
    (fun k hk z ↦ by
      rw [re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
      exact realifiedMatrixQuadraticForm_ge (hgap k hk) z) houter
  refine ⟨r₀, hr₀, hcap, ?_⟩
  intro r hr hrr u hsupp
  have hresult := h r hr hrr u hsupp
  rwa [energy_complexifyMatrix_eq_euclideanFrozenEnergy b u
    (integrable_of_supported u (Metric.ball 0 r) measurableSet_ball
      measure_ball_lt_top.ne hsupp)] at hresult

end JanetCartan.ContinuumNormal.FrozenModel
