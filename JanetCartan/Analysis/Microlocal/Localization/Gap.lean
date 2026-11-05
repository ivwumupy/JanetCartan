module

public import JanetCartan.Analysis.Fourier.Periodic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact nonstationary gap

The geometric part of `app:ch_osc:prop:osc-source-shell`. Frequencies in this file
are physical frequencies, so the periodic specialization uses `frequencyNorm`,
including its factor `2π`. No Fourier decay estimate is assumed or asserted here.
-/

@[expose] public noncomputable section

namespace JanetCartan.Localization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_osc:prop:osc-source-shell`: the complete Fourier phase, written with
a frequency covector. In Euclidean coordinates `ξ x` is the dot product. -/
def fourierPhase (φ : E → ℝ) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) (x : E) : ℝ :=
  ρ * φ x - ξ x

/-- `app:ch_osc:prop:osc-source-shell`: the derivative of the full phase is the
signed difference `ρ dφ - ξ`. Covector norms equal gradient norms in Euclidean space. -/
theorem fderiv_fourierPhase (φ : E → ℝ) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fourierPhase φ ρ ξ) x = ρ • fderiv ℝ φ x - ξ :=
  ((hφ.hasFDerivAt.const_mul ρ).sub ξ.hasFDerivAt).fderiv

/-- The physical frequency vector for the shared unit-torus convention,
used when applying `app:ch_osc:prop:osc-source-shell` to periodic coefficients. -/
def periodicFrequencyVector {n : ℕ} (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (2 * Real.pi) • WithLp.toLp 2 (fun i ↦ (k i : ℝ))

theorem norm_periodicFrequencyVector {n : ℕ} (k : Fin n → ℤ) :
    ‖periodicFrequencyVector k‖ = frequencyNorm k := by
  rw [periodicFrequencyVector, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rfl

/-- `app:ch_osc:prop:osc-source-shell`: a uniform gap constant for the two
components outside the annulus on which the multiplier equals one. -/
def radialGapConstant (c C : ℝ) : ℝ := min (c / (2 + c)) (C / (1 + 2 * C))

theorem radialGapConstant_pos {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    0 < radialGapConstant c C := by
  exact lt_min (by positivity) (by positivity)

/-- `app:ch_osc:prop:osc-source-shell`: the low-frequency component of the gap,
with the actual gradient vector `g`. -/
theorem low_frequency_gap {c ρ : ℝ} {g ξ : E}
    (hc : 0 < c) (hρ : 0 ≤ ρ) (hg : c ≤ ‖g‖) (hξ : ‖ξ‖ ≤ c * ρ / 2) :
    c / (2 + c) * (ρ + ‖ξ‖) ≤ ‖ρ • g - ξ‖ := by
  have hnorm : c * ρ - ‖ξ‖ ≤ ‖ρ • g - ξ‖ := by
    have h := norm_sub_norm_le (ρ • g) ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] at h
    nlinarith [mul_le_mul_of_nonneg_left hg hρ]
  apply le_trans _ hnorm
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 + c)).mpr
  nlinarith

/-- `app:ch_osc:prop:osc-source-shell`: the high-frequency component of the gap. -/
theorem high_frequency_gap {C ρ : ℝ} {g ξ : E}
    (hC : 0 < C) (hρ : 0 ≤ ρ) (hg : ‖g‖ ≤ C) (hξ : 2 * C * ρ ≤ ‖ξ‖) :
    C / (1 + 2 * C) * (ρ + ‖ξ‖) ≤ ‖ρ • g - ξ‖ := by
  have hnorm : ‖ξ‖ - C * ρ ≤ ‖ρ • g - ξ‖ := by
    have h := norm_sub_norm_le ξ (ρ • g)
    rw [norm_sub_rev, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ] at h
    nlinarith [mul_le_mul_of_nonneg_left hg hρ]
  apply le_trans _ hnorm
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 1 + 2 * C)).mpr
  nlinarith

/-- `app:ch_osc:prop:osc-source-shell`: a gap on the entire complement of the
plateau annulus, including the transition regions of a smooth cutoff. -/
theorem radial_frequency_gap {c C ρ : ℝ} {g ξ : E}
    (hc : 0 < c) (hC : 0 < C) (hρ : 0 ≤ ρ) (hgl : c ≤ ‖g‖) (hgu : ‖g‖ ≤ C)
    (hξ : ‖ξ‖ ≤ c * ρ / 2 ∨ 2 * C * ρ ≤ ‖ξ‖) :
    radialGapConstant c C * (ρ + ‖ξ‖) ≤ ‖ρ • g - ξ‖ := by
  have hp : 0 ≤ ρ + ‖ξ‖ := add_nonneg hρ (norm_nonneg _)
  rcases hξ with hl | hu
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hp).trans
      (low_frequency_gap hc hρ hgl hl)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hp).trans
      (high_frequency_gap hC hρ hgu hu)

/-- `app:ch_osc:prop:osc-source-shell`: the radial gap for the derivative of
the actual Fourier phase, not a linear approximation to it. -/
theorem fourierPhase_derivative_gap {c C ρ : ℝ} (φ : E → ℝ)
    (ξ : E →L[ℝ] ℝ) {x : E} (hφ : DifferentiableAt ℝ φ x)
    (hc : 0 < c) (hC : 0 < C) (hρ : 0 ≤ ρ)
    (hgl : c ≤ ‖fderiv ℝ φ x‖) (hgu : ‖fderiv ℝ φ x‖ ≤ C)
    (hξ : ‖ξ‖ ≤ c * ρ / 2 ∨ 2 * C * ρ ≤ ‖ξ‖) :
    radialGapConstant c C * (ρ + ‖ξ‖) ≤ ‖fderiv ℝ (fourierPhase φ ρ ξ) x‖ := by
  rw [fderiv_fourierPhase φ ρ ξ hφ]
  exact radial_frequency_gap hc hC hρ hgl hgu hξ

/-- `app:ch_osc:prop:osc-source-shell`: only the plateau condition on the
multiplier is needed to deduce the gap wherever its complement is nonzero. -/
theorem radial_frequency_gap_of_mask {c C ρ : ℝ} {g ξ : E} {π : E → ℂ}
    (hc : 0 < c) (hC : 0 < C) (hρ : 0 ≤ ρ) (hgl : c ≤ ‖g‖) (hgu : ‖g‖ ≤ C)
    (hπ : ∀ η, c * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * C * ρ → π η = 1)
    (hξ : 1 - π ξ ≠ 0) :
    radialGapConstant c C * (ρ + ‖ξ‖) ≤ ‖ρ • g - ξ‖ := by
  apply radial_frequency_gap hc hC hρ hgl hgu
  by_cases hl : ‖ξ‖ ≤ c * ρ / 2
  · exact Or.inl hl
  · right
    by_contra hu
    exact hξ (by rw [hπ ξ (le_of_not_ge hl) (le_of_not_ge hu), sub_self])

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:ch_osc:rem:osc-difference-frequency`: the positive size of the true
same-carrier frequency. Its signed phase is retained separately. -/
def differenceFrequency (lam z z' : ℝ) : ℝ := lam * |z - z'|

/-- `app:ch_osc:rem:osc-difference-frequency`: normalization of the signed
difference by its positive size. This definition does not replace the phase by
a Taylor approximation. -/
def normalizedDifferencePhase (φ ψ : E → ℝ) (z z' : ℝ) (x : E) : ℝ :=
  (φ x - ψ x) / |z - z'|

theorem differenceFrequency_pos {lam z z' : ℝ} (hlam : 0 < lam) (hz : z ≠ z') :
    0 < differenceFrequency lam z z' := by
  exact mul_pos hlam (abs_pos.mpr (sub_ne_zero.mpr hz))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:ch_osc:rem:osc-difference-frequency`: the normalized oscillation is
exactly the original signed difference, for either ordering of the parameters. -/
theorem differenceFrequency_mul_normalizedDifferencePhase
    (lam : ℝ) {z z' : ℝ} (hz : z ≠ z') (φ ψ : E → ℝ) (x : E) :
    differenceFrequency lam z z' * normalizedDifferencePhase φ ψ z z' x =
      lam * (φ x - ψ x) := by
  dsimp [differenceFrequency, normalizedDifferencePhase]
  have hd := sub_ne_zero.mpr hz
  have ha := abs_ne_zero.mpr hd
  field_simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- `app:ch_osc:rem:osc-difference-frequency`: passing from the smooth signed
quotient to a positive frequency must retain the sign `(z-z')/|z-z'|`. -/
theorem normalizedDifferencePhase_eq_signed_quotient
    {z z' : ℝ} (hz : z ≠ z') (φ ψ : E → ℝ) (x : E) :
    normalizedDifferencePhase φ ψ z z' x =
      ((z - z') / |z - z'|) * ((φ x - ψ x) / (z - z')) := by
  dsimp [normalizedDifferencePhase]
  have hd := sub_ne_zero.mpr hz
  have ha := abs_ne_zero.mpr hd
  field_simp

end JanetCartan.Localization
