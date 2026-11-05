module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.EuclideanSupportGap.Basic

/-!
# Finite physical supports and the Euclidean frozen gap

Cauchy–Schwarz and the final inner-radius choice for
`paper-v2.tex`, `app:ch_background:prop:bg-frame`. The low-frequency threshold,
symbol, image-error constant, and outer cap all precede the inner radius.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumNormal.EuclideanSupportGap

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "L²" => Lp (α := E) V 2 volume

/-- Finite a.e. support makes an L² input integrable, as required by the
Fourier bound in `app:ch_background:prop:bg-frame`. -/
theorem integrable_of_supported (u : L²) (s : Set E) (hs : MeasurableSet s)
    (hfinite : volume s ≠ ⊤) (hsupp : ∀ᵐ x, x ∉ s → u x = 0) :
    Integrable (u : E → V) := by
  let : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hfinite.lt_top⟩
  have h := ((Lp.memLp u).restrict s).integrable (by norm_num)
  apply (IntegrableOn.integrable_indicator (s := s) h hs).congr
  filter_upwards [hsupp] with x hx
  by_cases hxs : x ∈ s
  · simp [hxs]
  · simp [hxs, hx hxs]

/-- Cauchy–Schwarz on a finite measurable support, with the full Euclidean L²
norm (`app:ch_background:prop:bg-frame`). -/
theorem sq_integral_norm_le_support_volume (u : L²) (s : Set E)
    (hfinite : volume s ≠ ⊤) (hsupp : ∀ᵐ x, x ∉ s → u x = 0) :
    (∫ x, ‖u x‖) ^ 2 ≤ (volume s).toReal * ‖u‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hfinite.lt_top⟩
  have heq (p : ℕ) (hp : p ≠ 0) : (∫ x in s, ‖u x‖ ^ p) = ∫ x, ‖u x‖ ^ p := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupp] with x hx hxs
    simp [hx hxs, hp]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x ↦ norm_nonneg (u x)))
    (Filter.Eventually.of_forall (fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)))
    (by simpa using (Lp.memLp u).norm.restrict s)
    (by simpa using (memLp_const (μ := volume.restrict s) (p := 2) (1 : ℝ)))
  simp only [mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, mul_one] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, heq 2 (by decide),
    SingleChannel.integral_norm_sq_eq_norm_sq, Real.sqrt_sq (norm_nonneg u)] at h
  have heq1 : (∫ x in s, ‖u x‖) = ∫ x, ‖u x‖ := by simpa using heq 1 (by decide)
  rw [heq1] at h
  simp only [Measure.real, Measure.restrict_apply_univ] at h
  have hsq := (sq_le_sq₀ (integral_nonneg (fun x ↦ norm_nonneg (u x)))
    (by positivity : 0 ≤ ‖u‖ * Real.sqrt (volume s).toReal)).mpr h
  simpa only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, mul_comm] using hsq

/-- Absorb the low-frequency loss and any fixed image-comparison allowance
using physical support volume (`app:ch_background:prop:bg-frame`). This is a
bound for frozen energy; the parent must prove its actual image comparison. -/
theorem energy_sub_integral_error_ge_support_volume
    (b : E → V →L[ℂ] V) (hb : Continuous b)
    {c M R₀ C_image : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C_image)
    (hM : ∀ k, ‖b k‖ ≤ M) (hnonneg : ∀ k v, 0 ≤ (inner ℂ v (b k v)).re)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v, c * ‖v‖ ^ 2 ≤ (inner ℂ v (b k v)).re)
    (u : L²) (s : Set E) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (hsupp : ∀ᵐ x, x ∉ s → u x = 0) :
    (c - (lowFrequencyConstant n c R₀ + C_image) * (volume s).toReal) * ‖u‖ ^ 2 ≤
      energy b u - C_image * (∫ x, ‖u x‖) ^ 2 := by
  have hlow := energy_ge_sub_low_frequency b hb hc hM hnonneg hgap u
    (integrable_of_supported u s hs hfinite hsupp)
  have hcs := sq_integral_norm_le_support_volume u s hfinite hsupp
  have hD := add_nonneg (lowFrequencyConstant_nonneg (n := n) (R₀ := R₀) hc) hC
  have := mul_le_mul_of_nonneg_left hcs hD
  nlinarith

/-- Choose a positive inner physical radius below any prescribed cap, after
fixing the symbol and image-error allowance (`app:ch_background:prop:bg-frame`).
The conclusion is solely a frozen Fourier-energy gap, not actual row coercivity. -/
theorem exists_inner_radius_gap (hn : 0 < n)
    (b : E → V →L[ℂ] V) (hb : Continuous b)
    {c M R₀ C_image : ℝ} (hc : 0 < c) (hC : 0 ≤ C_image)
    (hM : ∀ k, ‖b k‖ ≤ M) (hnonneg : ∀ k v, 0 ≤ (inner ℂ v (b k v)).re)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v, c * ‖v‖ ^ 2 ≤ (inner ℂ v (b k v)).re)
    {r_outer : ℝ} (houter : 0 < r_outer) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r_outer ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : L²,
        (∀ᵐ x, x ∉ Metric.ball (0 : E) r → u x = 0) →
        c / 2 * ‖u‖ ^ 2 ≤ energy b u - C_image * (∫ x, ‖u x‖) ^ 2 := by
  let D := lowFrequencyConstant n c R₀ + C_image
  let v := (volume (Metric.ball (0 : E) 1)).toReal
  have hD : 0 ≤ D := add_nonneg (lowFrequencyConstant_nonneg hc.le) hC
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  let r₀ := min r_outer (min 1 (c / (2 * (D + 1) * (v + 1))))
  have hr₀ : 0 < r₀ := lt_min houter (lt_min zero_lt_one (by positivity))
  refine ⟨r₀, hr₀, min_le_left _ _, ?_⟩
  intro r hr hrr u hsupp
  have hr1 : r ≤ 1 := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrbound : r ≤ c / (2 * (D + 1) * (v + 1)) :=
    hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hvol : (volume (Metric.ball (0 : E) r)).toReal = r ^ n * v := by
    rw [Measure.addHaar_ball_of_pos volume (0 : E) hr]
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      finrank_euclideanSpace, v]
  have hpow : r ^ n ≤ r := by
    simpa using pow_le_pow_of_le_one hr.le hr1 hn
  have hsmall : D * (volume (Metric.ball (0 : E) r)).toReal ≤ c / 2 := by
    rw [hvol]
    have hbound := (le_div_iff₀ (by positivity : 0 < 2 * (D + 1) * (v + 1))).mp hrbound
    have hmono : D * (r ^ n * v) ≤ D * (r * v) := by gcongr
    have hprod : D * v ≤ (D + 1) * (v + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right hprod hr.le
    nlinarith
  have h := energy_sub_integral_error_ge_support_volume b hb hc.le hC hM hnonneg hgap
    u (Metric.ball (0 : E) r) measurableSet_ball measure_ball_lt_top.ne hsupp
  have := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
  dsimp [D] at this
  nlinarith

end JanetCartan.ContinuumNormal.EuclideanSupportGap
