module

public import JanetCartan.Analysis.Microlocal.Localization.Shell
public import JanetCartan.Analysis.Microlocal.Localization.Scales

/-!
# Spectral shell estimates with the paper scales

The spectral part of `app:ch_osc:prop:osc-source-shell`. Pointwise kernel decay
implies weighted integrability and the exact tail power. The negative estimate
combines this with the proved annular split and scale absorption. Application
to a physical source still requires Fourier identification and Plancherel.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.Localization

/-- `app:ch_osc:eq:osc-source-tail`: Conversion from the integration-by-parts ratio to
radial decay, retaining the exact derivative scale. -/
theorem scaleRatio_pow_eq_radialDecay {L R : ℝ} (hR : 0 < R) (q : ℕ) :
    (L / R) ^ q = L ^ q * R ^ (-(q : ℝ)) := by
  rw [div_pow, Real.rpow_neg hR.le, Real.rpow_natCast, div_eq_mul_inv]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_osc:eq:osc-source-tail`: Repeated-integration decay implies weighted integrability
at precisely `q > m+n/2`. -/
theorem integrable_sobolevEnergy_of_scaleRatio {ρ L m B : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hm : 0 ≤ m) (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q)
    {H : E → F} (hHm : AEStronglyMeasurable H μ)
    (hH : ∀ x, ‖H x‖ ≤ B * (L / (ρ + ‖x‖)) ^ q) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2) μ := by
  apply integrable_sobolevEnergy_of_decay hρ hm hq hHm (B := B * L ^ q)
  intro x
  simpa only [scaleRatio_pow_eq_radialDecay (by positivity : 0 < ρ + ‖x‖),
    mul_assoc] using hH x

/-- `app:ch_osc:eq:osc-source-tail`: The exact tail power `ρ^(m+n/2) (L/ρ)^q`,
with an explicit finite radial integral for the constant. -/
theorem fourierWeightedL2Norm_le_of_scaleRatio {ρ L m B : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) (hB : 0 ≤ B)
    {H : E → F} (hHm : AEStronglyMeasurable H μ)
    (hH : ∀ x, ‖H x‖ ≤ B * (L / (ρ + ‖x‖)) ^ q) :
    fourierWeightedL2Norm μ m H ≤
      (B * Real.sqrt (∫ x : E, (1 + ‖x‖) ^ (-(2 * (q : ℝ) - 2 * m)) ∂μ)) *
        (ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2) * (L / ρ) ^ q) := by
  have hd : ∀ x, ‖H x‖ ≤ (B * L ^ q) * (ρ + ‖x‖) ^ (-(q : ℝ)) := by
    intro x
    simpa only [scaleRatio_pow_eq_radialDecay (by positivity : 0 < ρ + ‖x‖),
      mul_assoc] using hH x
  apply (fourierWeightedL2Norm_le_of_decay hρ hm hq (by positivity) hHm hd).trans_eq
  rw [Real.rpow_sub (by positivity : 0 < ρ), Real.rpow_natCast, div_pow]
  ring

variable [NormedSpace ℂ F]

/-- `app:ch_osc:eq:osc-source-negative`: The negative Sobolev gain follows from L² control,
pointwise complementary decay, and the fixed scale gap. The annular split inequality is proved,
not assumed. -/
theorem fourierWeightedL2Norm_negative_le_of_scaleRatio {ρ L c σ M B₀ B : ℝ} {q : ℕ}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hc : 0 < c) (hM : 0 ≤ M)
    (hgap : L ≤ ρ ^ (1 - σ)) (hq : (Module.finrank ℝ E : ℝ) / 2 < q)
    (horder : M + (Module.finrank ℝ E : ℝ) / 2 ≤ σ * q) (hB : 0 ≤ B)
    (π : E → ℂ) (H : E → F) (hπ : ∀ x, ‖x‖ < c * ρ → π x = 0)
    (hH : Integrable (fun x ↦ ‖H x‖ ^ 2) μ)
    (htm : AEStronglyMeasurable (fun x ↦ (1 - π x) • H x) μ)
    (h₀ : fourierWeightedL2Norm μ 0 H ≤ B₀)
    (ht : ∀ x, ‖(1 - π x) • H x‖ ≤ B * (L / (ρ + ‖x‖)) ^ q) :
    fourierWeightedL2Norm μ (-M) H ≤
      (c ^ (-M) * B₀ + B * Real.sqrt
        (∫ x : E, (1 + ‖x‖) ^ (-(2 * (q : ℝ))) ∂μ)) * ρ ^ (-M) := by
  have hqi : (0 : ℝ) + (Module.finrank ℝ E : ℝ) / 2 < q := by simpa using hq
  have hti : Integrable (fun x ↦ ‖(1 - π x) • H x‖ ^ 2) μ := by
    simpa using integrable_sobolevEnergy_of_scaleRatio hρ (m := 0) le_rfl hqi htm ht
  have htail := fourierWeightedL2Norm_le_of_scaleRatio hρ hL (m := 0) le_rfl hqi hB htm ht
  simp only [mul_zero, sub_zero, zero_add] at htail
  have habs := tail_factor_le_negative_power hρ hL hgap horder
  calc
    _ ≤ (c * ρ) ^ (-M) * fourierWeightedL2Norm μ 0 H +
        fourierWeightedL2Norm μ 0 (fun x ↦ (1 - π x) • H x) :=
      fourierWeightedL2Norm_negative_le_annular_split hc (by positivity) hM π H hπ hH hti
    _ ≤ (c * ρ) ^ (-M) * B₀ +
        (B * Real.sqrt (∫ x : E, (1 + ‖x‖) ^ (-(2 * (q : ℝ))) ∂μ)) * ρ ^ (-M) := by
      apply add_le_add (mul_le_mul_of_nonneg_left h₀ (by positivity))
      exact htail.trans (mul_le_mul_of_nonneg_left habs (by positivity))
    _ = _ := by rw [Real.mul_rpow hc.le (by positivity : 0 ≤ ρ)]; ring

/-- `app:ch_osc:eq:osc-source-negative` at the paper's separated-carrier scales. The
integration order can be chosen using `exists_tail_order` with the fixed gap `13/338`. -/
theorem fourierWeightedL2Norm_negative_le_of_separated_carrier
    {T ρ L c M B₀ B : ℝ} {q : ℕ}
    (hT : 0 ≤ T) (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hc : 0 < c) (hM : 0 ≤ M)
    (hfreq : T ^ (carrierExponent - separationExponent) ≤ ρ)
    (hscale : L ≤ T ^ (1 + meanSlack)) (hq : (Module.finrank ℝ E : ℝ) / 2 < q)
    (horder : M + (Module.finrank ℝ E : ℝ) / 2 ≤ separatedCarrierGap * q) (hB : 0 ≤ B)
    (π : E → ℂ) (H : E → F) (hπ : ∀ x, ‖x‖ < c * ρ → π x = 0)
    (hH : Integrable (fun x ↦ ‖H x‖ ^ 2) μ)
    (htm : AEStronglyMeasurable (fun x ↦ (1 - π x) • H x) μ)
    (h₀ : fourierWeightedL2Norm μ 0 H ≤ B₀)
    (ht : ∀ x, ‖(1 - π x) • H x‖ ≤ B * (L / (ρ + ‖x‖)) ^ q) :
    fourierWeightedL2Norm μ (-M) H ≤
      (c ^ (-M) * B₀ + B * Real.sqrt
        (∫ x : E, (1 + ‖x‖) ^ (-(2 * (q : ℝ))) ∂μ)) * ρ ^ (-M) :=
  fourierWeightedL2Norm_negative_le_of_scaleRatio hρ hL hc hM
    (scale_gap_of_separated_carrier hT hfreq hscale) hq horder hB π H hπ hH htm h₀ ht

end JanetCartan.Localization
