module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# Actual Euclidean envelope cutoff

The low/high split in `app:ch_response:thm:response-literal-transfer` is made
on Euclidean Lebesgue L² classes. The symbol below is in Mathlib's frequency
variable ξ; the physical covector is η = 2πξ. No torus identification is used.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- Input cutoff for the complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. Its fields describe the given
symbol, not any estimate on the resulting high-frequency datum. -/
structure EnvelopeCutoff (d : ℕ) (Λ B R : ℝ) where
  symbol : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ ∞ symbol
  bound_nonneg : 0 ≤ B
  bound : ∀ ξ, |symbol ξ| ≤ B
  one_on_ball : ∀ ξ, ‖ξ‖ ≤ Λ → symbol ξ = 1
  zero_outside : ∀ ξ, R * Λ ≤ ‖ξ‖ → symbol ξ = 0

namespace EnvelopeCutoff

variable {Λ B R : ℝ} (χ : EnvelopeCutoff d Λ B R)

/-- The cutoff times the actual Fourier transform is square integrable;
this supplies the low piece in `app:ch_response:thm:response-literal-transfer`. -/
theorem memLp_symbol_fourier (f : L2) :
    MemLp (fun ξ ↦ χ.symbol ξ • (𝓕 f) ξ) 2 volume := by
  apply ((Lp.memLp (𝓕 f)).const_smul B).mono
    (χ.smooth.continuous.aestronglyMeasurable.smul (Lp.memLp (𝓕 f)).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖χ.symbol ξ • (𝓕 f : L2) ξ‖ ≤ ‖B • (𝓕 f : L2) ξ‖
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg χ.bound_nonneg]
  exact mul_le_mul_of_nonneg_right (χ.bound ξ) (norm_nonneg _)

/-- Actual low envelope, using the L² inverse Fourier transform, in
`app:ch_response:thm:response-literal-transfer`. -/
def low (f : L2) : L2 := 𝓕⁻ ((χ.memLp_symbol_fourier f).toLp _)

/-- Actual complementary high envelope in
`app:ch_response:thm:response-literal-transfer`. -/
def high (f : L2) : L2 := f - χ.low f

/-- Exact L² reconstruction in `app:ch_response:thm:response-literal-transfer`. -/
theorem low_add_high (f : L2) : χ.low f + χ.high f = f := by
  simp [high]

/-- Fourier representative of the low piece in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_low_ae (f : L2) :
    (𝓕 (χ.low f) : L2) =ᵐ[volume] fun ξ ↦ χ.symbol ξ • (𝓕 f) ξ := by
  simpa only [low, fourier_fourierInv_eq] using (χ.memLp_symbol_fourier f).coeFn_toLp

/-- Fourier representative of the high piece in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_high_ae (f : L2) :
    (𝓕 (χ.high f) : L2) =ᵐ[volume] fun ξ ↦ (1 - χ.symbol ξ) • (𝓕 f) ξ := by
  have hf : 𝓕 (χ.high f) = 𝓕 f - 𝓕 (χ.low f) := by
    exact map_sub (fourierCLM ℂ L2) _ _
  rw [hf]
  filter_upwards [Lp.coeFn_sub (𝓕 f) (𝓕 (χ.low f)), χ.fourier_low_ae f] with ξ hξ hlow
  simp only [hξ, Pi.sub_apply, hlow, sub_smul, one_smul]

/-- The actual lower envelope vanishes outside the prescribed frequency ball,
as needed by the low-envelope consumer of
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_low_zero_outside (f : L2) :
    ∀ᵐ ξ ∂volume, R * Λ ≤ ‖ξ‖ → (𝓕 (χ.low f) : L2) ξ = 0 := by
  filter_upwards [χ.fourier_low_ae f] with ξ hξ hball
  simp [hξ, χ.zero_outside ξ hball]

/-- The actual high envelope vanishes on the cutoff ball in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_high_zero_on_ball (f : L2) :
    ∀ᵐ ξ ∂volume, ‖ξ‖ ≤ Λ → (𝓕 (χ.high f) : L2) ξ = 0 := by
  filter_upwards [χ.fourier_high_ae f] with ξ hξ hball
  simp [hξ, χ.one_on_ball ξ hball]

/-- Convert a cutoff specified in the physical covector η to Mathlib's
frequency ξ, where η = 2πξ. This is the literal multiplier conversion in
`app:ch_response:thm:response-literal-transfer`. -/
def physicalCovectorCutoff : EnvelopeCutoff d (Λ / (2 * Real.pi)) B R where
  symbol ξ := χ.symbol ((2 * Real.pi) • ξ)
  smooth := χ.smooth.comp (contDiff_id.const_smul (2 * Real.pi))
  bound_nonneg := χ.bound_nonneg
  bound ξ := χ.bound _
  one_on_ball ξ hξ := by
    apply χ.one_on_ball
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hξ
      |> fun h ↦ by linarith
  zero_outside ξ hξ := by
    apply χ.zero_outside
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have he : R * (Λ / (2 * Real.pi)) = (R * Λ) / (2 * Real.pi) := by ring
    rw [he] at hξ
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hξ
    linarith

/-- The converted low operator uses exactly the symbol χ(2πξ), not χ(ξ), in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_physical_low_ae (f : L2) :
    (𝓕 (χ.physicalCovectorCutoff.low f) : L2) =ᵐ[volume]
      fun ξ ↦ χ.symbol ((2 * Real.pi) • ξ) • (𝓕 f) ξ :=
  χ.physicalCovectorCutoff.fourier_low_ae f

end EnvelopeCutoff
end JanetCartan.ResponseTransfer.Complement
