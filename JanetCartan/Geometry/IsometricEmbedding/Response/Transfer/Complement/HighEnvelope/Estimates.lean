module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.HighEnvelope.Cutoff

/-!
# High-envelope Sobolev estimates

The displayed high-envelope bound in
`app:ch_response:thm:response-literal-transfer`. All real-valued norm
comparisons retain finite membership of the dominating weighted transform.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

private theorem sobolev_bound_of_ae {s p C : ℝ} {u f : L2}
    (hC : 0 ≤ C) (hf : MemFourierSobolev p f)
    (h : ∀ᵐ ξ ∂volume, ‖weightedL2Fourier s u ξ‖ ≤ C * ‖weightedL2Fourier p f ξ‖) :
    MemFourierSobolev s u ∧ fourierSobolevNorm s u ≤ C * fourierSobolevNorm p f := by
  have h' : ∀ᵐ ξ ∂volume,
      ‖weightedL2Fourier s u ξ‖ ≤ ‖(C • weightedL2Fourier p f) ξ‖ := by
    simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using h
  refine ⟨(hf.const_smul C).mono (aestronglyMeasurable_weightedL2Fourier s u) h', ?_⟩
  have hn := ENNReal.toReal_mono (hf.const_smul C).eLpNorm_ne_top
    (eLpNorm_mono_ae (aestronglyMeasurable_weightedL2Fourier s u) h')
  simpa only [eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg hC, ENNReal.toReal_ofReal hC, fourierSobolevNorm] using hn

private theorem weight_tail_bound {Λ t p : ℝ} (hΛ : 0 < Λ) (htp : t ≤ p)
    (ξ : E) (hξ : Λ ≤ ‖ξ‖) :
    euclideanSobolevWeight t ξ ≤ Λ ^ (t - p) * euclideanSobolevWeight p ξ := by
  have hbase : Λ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ]
  have hpow := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hΛ) hbase
    (show (t - p) / 2 ≤ 0 by linarith)
  rw [← Real.rpow_natCast_mul hΛ.le 2, Nat.cast_ofNat,
    show (2 : ℝ) * ((t - p) / 2) = t - p by ring] at hpow
  calc
    euclideanSobolevWeight t ξ =
        euclideanSobolevWeight (t - p) ξ * euclideanSobolevWeight p ξ := by
      rw [← euclideanSobolevWeight_add, sub_add_cancel]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (euclideanSobolevWeight_pos p ξ).le

namespace EnvelopeCutoff

variable {Λ B R : ℝ} (χ : EnvelopeCutoff d Λ B R)

/-- The compact Fourier support gives every nonnegative Sobolev order of the
actual low envelope in `app:ch_response:thm:response-literal-transfer`. -/
theorem low_regularization_bound {s : ℝ} (hs : 0 ≤ s) (f : L2) :
    MemFourierSobolev s (χ.low f) ∧
      fourierSobolevNorm s (χ.low f) ≤
        (1 + (R * Λ) ^ 2) ^ (s / 2) * B * ‖f‖ := by
  have hB := χ.bound_nonneg
  have h := sobolev_bound_of_ae
    (u := χ.low f) (s := s) (C := (1 + (R * Λ) ^ 2) ^ (s / 2) * B)
    (by positivity) (memFourierSobolev_zero f)
  simp only [fourierSobolevNorm_zero] at h
  apply h
  filter_upwards [χ.fourier_low_ae f] with ξ hξ
  simp only [norm_weightedL2Fourier, hξ, norm_smul, Real.norm_eq_abs,
    euclideanSobolevWeight_zero, one_mul]
  by_cases hout : R * Λ ≤ ‖ξ‖
  · rw [χ.zero_outside ξ hout]
    simp only [abs_zero, zero_mul, mul_zero]
    positivity
  · have hξR : ‖ξ‖ ≤ R * Λ := (lt_of_not_ge hout).le
    have hw : euclideanSobolevWeight s ξ ≤ (1 + (R * Λ) ^ 2) ^ (s / 2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith [norm_nonneg ξ]
    calc
      _ ≤ (1 + (R * Λ) ^ 2) ^ (s / 2) * (B * ‖(𝓕 f : L2) ξ‖) :=
        mul_le_mul hw (mul_le_mul_of_nonneg_right (χ.bound ξ) (norm_nonneg _))
          (by positivity) (by positivity)
      _ = _ := by ring

/-- All real Sobolev memberships of the low envelope required by the
complete-complement argument of `app:ch_response:thm:response-literal-transfer`. -/
theorem low_mem_all_orders (s : ℝ) (f : L2) : MemFourierSobolev s (χ.low f) :=
  ((χ.low_regularization_bound (s := max 0 s) (le_max_left _ _) f).1).mono
    (le_max_right _ _)

/-- Sobolev membership and bound for the actual low envelope, at the input order,
for `app:ch_response:thm:response-literal-transfer`. -/
theorem low_sobolev_bound {p : ℝ} {f : L2} (hf : MemFourierSobolev p f) :
    MemFourierSobolev p (χ.low f) ∧
      fourierSobolevNorm p (χ.low f) ≤ B * fourierSobolevNorm p f := by
  apply sobolev_bound_of_ae χ.bound_nonneg hf
  filter_upwards [χ.fourier_low_ae f] with ξ hξ
  simp only [norm_weightedL2Fourier, hξ, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ euclideanSobolevWeight p ξ * (B * ‖(𝓕 f : L2) ξ‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (χ.bound ξ) (norm_nonneg _))
        (euclideanSobolevWeight_pos p ξ).le
    _ = _ := by ring

/-- The uniform bound used for the bounded-frequency range of
`app:ch_response:thm:response-literal-transfer`. No lower bound on Λ is needed. -/
theorem high_sobolev_bound {p : ℝ} {f : L2} (hf : MemFourierSobolev p f) :
    MemFourierSobolev p (χ.high f) ∧
      fourierSobolevNorm p (χ.high f) ≤ (1 + B) * fourierSobolevNorm p f := by
  apply sobolev_bound_of_ae (by linarith [χ.bound_nonneg]) hf
  filter_upwards [χ.fourier_high_ae f] with ξ hξ
  simp only [norm_weightedL2Fourier, hξ, norm_smul, Real.norm_eq_abs]
  have hb : |1 - χ.symbol ξ| ≤ 1 + B := by
    calc
      _ ≤ |(1 : ℝ)| + |χ.symbol ξ| := by simpa only [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (χ.symbol ξ)
      _ ≤ _ := by simpa using add_le_add_left (χ.bound ξ) 1
  calc
    _ ≤ euclideanSobolevWeight p ξ * ((1 + B) * ‖(𝓕 f : L2) ξ‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
        (euclideanSobolevWeight_pos p ξ).le
    _ = _ := by ring

/-- The high-envelope estimate in
`app:ch_response:thm:response-literal-transfer`, including finite membership.
It holds for every positive cutoff radius, hence in particular Λ ≥ 1. -/
theorem high_tail_bound {t p : ℝ} (hΛ : 0 < Λ) (htp : t ≤ p)
    {f : L2} (hf : MemFourierSobolev p f) :
    MemFourierSobolev t (χ.high f) ∧
      fourierSobolevNorm t (χ.high f) ≤
        (1 + B) * Λ ^ (t - p) * fourierSobolevNorm p f := by
  have hB := χ.bound_nonneg
  apply sobolev_bound_of_ae (by positivity) hf
  filter_upwards [χ.fourier_high_ae f] with ξ hξ
  simp only [norm_weightedL2Fourier, hξ, norm_smul, Real.norm_eq_abs]
  by_cases hball : ‖ξ‖ ≤ Λ
  · rw [χ.one_on_ball ξ hball]
    simp only [sub_self, abs_zero, zero_mul, mul_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (euclideanSobolevWeight_pos p ξ).le (norm_nonneg _))
  · have hw := weight_tail_bound hΛ htp ξ (le_of_not_ge hball)
    have hb : |1 - χ.symbol ξ| ≤ 1 + B := by
      calc
        _ ≤ |(1 : ℝ)| + |χ.symbol ξ| := by simpa only [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (χ.symbol ξ)
        _ ≤ _ := by simpa using add_le_add_left (χ.bound ξ) 1
    calc
      _ ≤ (Λ ^ (t - p) * euclideanSobolevWeight p ξ) *
          ((1 + B) * ‖(𝓕 f : L2) ξ‖) := by
            apply mul_le_mul hw (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
              (by positivity)
            exact mul_nonneg (Real.rpow_pos_of_pos hΛ _).le (euclideanSobolevWeight_pos p ξ).le
      _ = _ := by ring

/-- The high-envelope estimate with a cutoff given in physical covectors,
for `app:ch_response:thm:response-literal-transfer`. The normalization cost
`(2π)^(p-t)` is explicit. -/
theorem high_physical_tail_bound {t p : ℝ} (hΛ : 0 < Λ) (htp : t ≤ p)
    {f : L2} (hf : MemFourierSobolev p f) :
    MemFourierSobolev t (χ.physicalCovectorCutoff.high f) ∧
      fourierSobolevNorm t (χ.physicalCovectorCutoff.high f) ≤
        ((1 + B) * (2 * Real.pi) ^ (p - t)) * Λ ^ (t - p) * fourierSobolevNorm p f := by
  have h := χ.physicalCovectorCutoff.high_tail_bound (div_pos hΛ (by positivity)) htp hf
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [Real.div_rpow hΛ.le (by positivity), show p - t = -(t - p) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi)]
  ring

/-- Bounded-radius case of the displayed high-envelope estimate in
`app:ch_response:thm:response-literal-transfer`, deduced from the uniform
multiplier bound. This retains the fixed-scale cost when Λ < 1. -/
theorem high_bounded_radius_bound {t p : ℝ} (hΛ : 0 < Λ) (hΛ₁ : Λ ≤ 1)
    (htp : t ≤ p) {f : L2} (hf : MemFourierSobolev p f) :
    MemFourierSobolev t (χ.high f) ∧
      fourierSobolevNorm t (χ.high f) ≤
        (1 + B) * Λ ^ (t - p) * fourierSobolevNorm p f := by
  obtain ⟨hm, hn⟩ := χ.high_sobolev_bound hf
  refine ⟨hm.mono htp, (fourierSobolevNorm_mono hm htp).trans (hn.trans ?_)⟩
  have hpow := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΛ hΛ₁ (sub_nonpos.mpr htp)
  have hB := χ.bound_nonneg
  calc
    (1 + B) * fourierSobolevNorm p f =
        (1 + B) * 1 * fourierSobolevNorm p f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (fourierSobolevNorm_nonneg p f)

end EnvelopeCutoff
end JanetCartan.ResponseTransfer.Complement
