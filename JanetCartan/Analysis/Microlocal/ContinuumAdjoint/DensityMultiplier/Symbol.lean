module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.WeightedL2

/-!
# The literal angular and high-frequency density symbol

The multiplier in `app:ch_background:eq:bg-density-adjoint` retains the angular
argument `η / |η|` and the half-order factor. Values of the angular function at
zero are harmless because the high-frequency cutoff vanishes there. This file
proves measurability and weighted L² estimates from bounds on the unit directions;
the full mixed derivative estimate remains a separate obligation.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier

open ContinuumRow RawCutoffBounds

variable {n : ℕ}

/-- The fixed angular and high-frequency mask before the half-order multiplier
(`app:ch_background:eq:bg-density-adjoint`). The second argument of `ρ` is a
unit direction away from zero, not an auxiliary torus coordinate. -/
def angularHighMask (ρ : CarrierVariable n → ℂ) (χ : ℝ → ℝ)
    (x : CarrierVariable n) : ℂ :=
  χ ‖x.2‖ • ρ (x.1, ‖x.2‖⁻¹ • x.2)

/-- The paper's exact full-frequency symbol
`ρ(z,η̂) χ_hi(|η|) |η|^(1/2)` (`app:ch_background:eq:bg-density-adjoint`). -/
def densityFrequencySymbol (ρ : CarrierVariable n → ℂ) (χ : ℝ → ℝ) :
    CarrierVariable n → ℂ := halfOrderCoefficient (angularHighMask ρ χ)

/-- Measurability of the normalized angular mask, including the value at zero
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem measurable_angularHighMask {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : Measurable ρ) (hχ : Measurable χ) : Measurable (angularHighMask ρ χ) := by
  unfold angularHighMask
  exact (hχ.comp measurable_snd.norm).smul
    (hρ.comp (measurable_fst.prodMk (measurable_snd.norm.inv.smul measurable_snd)))

/-- A bound on unit angular directions suffices for the literal full mask.
No angular bound at zero is needed (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_angularHighMask_le {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0) (x : CarrierVariable n) :
    ‖angularHighMask ρ χ x‖ ≤ M := by
  by_cases hx : x.2 = 0
  · simpa [angularHighMask, hx, hχ0] using hM
  · have hn : ‖‖x.2‖⁻¹ • x.2‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    calc
      _ = |χ ‖x.2‖| * ‖ρ (x.1, ‖x.2‖⁻¹ • x.2)‖ := by
        rw [angularHighMask, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * M := mul_le_mul (hχ _) (hρ _ _ hn) (norm_nonneg _) (by norm_num)
      _ = M := one_mul _

/-- Exact low-frequency vanishing of the density symbol, with no upper cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityFrequencySymbol_eq_zero_of_low (ρ : CarrierVariable n → ℂ)
    {χ : ℝ → ℝ} (hχ : ∀ r ≤ 1, χ r = 0) (x : CarrierVariable n) (hx : ‖x.2‖ ≤ 1) :
    densityFrequencySymbol ρ χ x = 0 := by
  simp [densityFrequencySymbol, halfOrderCoefficient, angularHighMask, hχ _ hx]

/-- Above the fixed transition region the exact symbol is `|η|^(1/2) ρ(z,η̂)`.
There is no frequency ceiling (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityFrequencySymbol_eq_of_high (ρ : CarrierVariable n → ℂ)
    {χ : ℝ → ℝ} (hχ : ∀ r, 2 ≤ r → χ r = 1) (x : CarrierVariable n)
    (hx : 2 ≤ ‖x.2‖) :
    densityFrequencySymbol ρ χ x =
      (Real.sqrt ‖x.2‖ : ℂ) * ρ (x.1, ‖x.2‖⁻¹ • x.2) := by
  simp [densityFrequencySymbol, halfOrderCoefficient, angularHighMask, hχ _ hx]

/-- Weighted output for the literal angular symbol, on the entire frequency
space. The input is any weighted member of the existing carrier L² space
(`app:ch_background:eq:bg-density-adjoint`). -/
def densityFrequencyOutput (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    CarrierL2 n :=
  weightedHalfOrderOutput s (measurable_angularHighMask hρmeas hχmeas).aestronglyMeasurable
    hM (Filter.Eventually.of_forall (norm_angularHighMask_le hM hρ hχ hχ0)) f hf

/-- The actual symbol is retained by the weighted L² construction
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityFrequencyOutput_coeFn (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    densityFrequencyOutput s hρmeas hχmeas hM hρ hχ hχ0 f hf =ᵐ[carrierMeasure n]
      fun x ↦ etaBesselWeight s x • (densityFrequencySymbol ρ χ x * f x) :=
  weightedHalfOrderOutput_coeFn _ _ _ _ _ _

/-- The frequency-side density bound for the literal angular/high mask. Its
constant is uniform in frequency and in the input (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityFrequencyOutput_le (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    ‖densityFrequencyOutput s hρmeas hχmeas hM hρ hχ hχ0 f hf‖ ≤
      M * carrierWeightedNorm (etaBesselWeight (s + 1)) f hf :=
  norm_weightedHalfOrderOutput_le _ _ _ _ _ _

end JanetCartan.ContinuumAdjoint.DensityMultiplier
