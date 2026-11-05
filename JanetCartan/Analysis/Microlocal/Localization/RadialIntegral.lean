module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial integration of Fourier tails

The frequency integral in `app:ch_osc:prop:osc-source-shell`, including its exact
integrability threshold and scale power. The final theorem applies to arbitrary
measurable finite- or infinite-dimensional frequency data satisfying pointwise
decay. Identifying these data with the Fourier transform of the parameterized
oscillatory source is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.Localization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Pointwise radial rescaling. -/
theorem radialDecay_eq_rescaled {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) (x : E) :
    (ρ + ‖x‖) ^ (-s) = ρ ^ (-s) * (1 + ‖ρ⁻¹ • x‖) ^ (-s) := by
  rw [← Real.mul_rpow hρ.le (by positivity)]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  field_simp

/-- `app:ch_osc:prop:osc-source-shell`: Radial decay is integrable when its order exceeds the
dimension. -/
theorem integrable_radialDecay {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : (Module.finrank ℝ E : ℝ) < s) :
    Integrable (fun x : E ↦ (ρ + ‖x‖) ^ (-s)) μ := by
  simp_rw [radialDecay_eq_rescaled hρ]
  exact ((integrable_one_add_norm (μ := μ) hs).comp_smul (inv_ne_zero hρ.ne')).const_mul _

/-- `app:ch_osc:prop:osc-source-shell`: Exact rescaling of the radial decay integral. -/
theorem integral_radialDecay {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    (∫ x : E, (ρ + ‖x‖) ^ (-s) ∂μ) =
      ρ ^ ((Module.finrank ℝ E : ℝ) - s) * ∫ x : E, (1 + ‖x‖) ^ (-s) ∂μ := by
  simp_rw [radialDecay_eq_rescaled hρ]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ (fun x : E ↦ (1 + ‖x‖) ^ (-s)) hρ.le,
    smul_eq_mul, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hρ]
  congr 2
  ring

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The Sobolev weight costs `2m` powers of radial decay. -/
theorem sobolevWeight_mul_radialDecay_le {ρ m q : ℝ} (hρ : 1 ≤ ρ) (hm : 0 ≤ m) (x : E) :
    (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q) ≤ (ρ + ‖x‖) ^ (-(2 * q - 2 * m)) := by
  have hp : 0 < ρ + ‖x‖ := by positivity
  have hb : 1 + ‖x‖ ^ 2 ≤ (ρ + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have hpow : (1 + ‖x‖ ^ 2) ^ m ≤ (ρ + ‖x‖) ^ (2 * m) := by
    calc
      _ ≤ ((ρ + ‖x‖) ^ 2) ^ m := Real.rpow_le_rpow (by positivity) hb hm
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
  calc
    _ ≤ (ρ + ‖x‖) ^ (2 * m) * (ρ + ‖x‖) ^ (-2 * q) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

/-- `app:ch_osc:prop:osc-source-shell`: The exact source threshold `q > m + n/2` gives
integrability. -/
theorem integrable_sobolevWeight_mul_radialDecay {ρ m q : ℝ} (hρ : 1 ≤ ρ) (hm : 0 ≤ m)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) :
    Integrable (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q)) μ := by
  have hg := integrable_radialDecay (μ := μ) (by linarith : 0 < ρ)
    (show (Module.finrank ℝ E : ℝ) < 2 * q - 2 * m by linarith)
  apply hg.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sobolevWeight_mul_radialDecay_le hρ hm x

/-- `app:ch_osc:prop:osc-source-shell`: The weighted frequency integral has the power `ρ ^
(2m+n-2q)`. -/
theorem integral_sobolevWeight_mul_radialDecay_le {ρ m q : ℝ} (hρ : 1 ≤ ρ) (hm : 0 ≤ m)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) :
    (∫ x : E, (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q) ∂μ) ≤
      ρ ^ (2 * m + (Module.finrank ℝ E : ℝ) - 2 * q) *
        ∫ x : E, (1 + ‖x‖) ^ (-(2 * q - 2 * m)) ∂μ := by
  have hρp : 0 < ρ := by linarith
  calc
    _ ≤ ∫ x : E, (ρ + ‖x‖) ^ (-(2 * q - 2 * m)) ∂μ :=
      integral_mono (integrable_sobolevWeight_mul_radialDecay hρ hm hq)
        (integrable_radialDecay hρp (by linarith)) (sobolevWeight_mul_radialDecay_le hρ hm)
    _ = _ := by rw [integral_radialDecay hρp]; congr 2; ring

/-- `app:ch_osc:prop:osc-source-shell`: Taking square roots gives the power `ρ ^ (m+n/2-q)`. -/
theorem sqrt_integral_sobolevWeight_mul_radialDecay_le {ρ m q : ℝ} (hρ : 1 ≤ ρ) (hm : 0 ≤ m)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) :
    Real.sqrt (∫ x : E, (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q) ∂μ) ≤
      Real.sqrt (∫ x : E, (1 + ‖x‖) ^ (-(2 * q - 2 * m)) ∂μ) *
        ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2 - q) := by
  apply (Real.sqrt_le_sqrt (integral_sobolevWeight_mul_radialDecay_le hρ hm hq)).trans_eq
  rw [Real.sqrt_mul (by positivity), mul_comm]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ ρ)]
  congr 1
  ring

variable {F : Type*} [NormedAddCommGroup F]

/-- `app:ch_osc:prop:osc-source-shell`: the frequency-side Bessel weighted L² quantity.
Applications must also establish integrability of the energy density. -/
def fourierWeightedL2Norm (μ : Measure E) (m : ℝ) (H : E → F) : ℝ :=
  Real.sqrt (∫ x : E, (1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2 ∂μ)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Pointwise decay bounds the weighted energy density. -/
theorem sobolevEnergy_le_of_decay {ρ m q B : ℝ} (hρ : 1 ≤ ρ)
    {H : E → F} (hH : ∀ x, ‖H x‖ ≤ B * (ρ + ‖x‖) ^ (-q)) (x : E) :
    (1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2 ≤ B ^ 2 * ((1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q)) := by
  have hp : 0 < ρ + ‖x‖ := by positivity
  have hb : ‖H x‖ ^ 2 ≤ B ^ 2 * (ρ + ‖x‖) ^ (-2 * q) := by
    calc
      _ ≤ (B * (ρ + ‖x‖) ^ (-q)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hH x) 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast ((ρ + ‖x‖) ^ (-q)), ← Real.rpow_mul hp.le]
        congr 2
        ring
  calc
    _ ≤ (1 + ‖x‖ ^ 2) ^ m * (B ^ 2 * (ρ + ‖x‖) ^ (-2 * q)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- `app:ch_osc:prop:osc-source-shell`: Measurability and pointwise decay imply genuine weighted
integrability. -/
theorem integrable_sobolevEnergy_of_decay {ρ m q B : ℝ} (hρ : 1 ≤ ρ)
    (hm : 0 ≤ m) (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q)
    {H : E → F} (hHm : AEStronglyMeasurable H μ)
    (hH : ∀ x, ‖H x‖ ≤ B * (ρ + ‖x‖) ^ (-q)) :
    Integrable (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ m * ‖H x‖ ^ 2) μ := by
  apply ((integrable_sobolevWeight_mul_radialDecay (μ := μ) hρ hm hq).const_mul (B ^ 2)).mono'
  · exact (by fun_prop : AEStronglyMeasurable (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ m) μ).mul
      (hHm.norm.pow 2)
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sobolevEnergy_le_of_decay hρ hH x

/-- `app:ch_osc:prop:osc-source-shell`: The Fourier-side tail bound, conditional on pointwise
decay of the frequency data. The constant is an explicit convergent integral. -/
theorem fourierWeightedL2Norm_le_of_decay {ρ m q B : ℝ} (hρ : 1 ≤ ρ)
    (hm : 0 ≤ m) (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q) (hB : 0 ≤ B)
    {H : E → F} (hHm : AEStronglyMeasurable H μ)
    (hH : ∀ x, ‖H x‖ ≤ B * (ρ + ‖x‖) ^ (-q)) :
    fourierWeightedL2Norm μ m H ≤
      B * Real.sqrt (∫ x : E, (1 + ‖x‖) ^ (-(2 * q - 2 * m)) ∂μ) *
        ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2 - q) := by
  have he := integral_mono (integrable_sobolevEnergy_of_decay hρ hm hq hHm hH)
    ((integrable_sobolevWeight_mul_radialDecay (μ := μ) hρ hm hq).const_mul (B ^ 2))
    (sobolevEnergy_le_of_decay hρ hH)
  rw [integral_const_mul] at he
  calc
    _ ≤ Real.sqrt (B ^ 2 * ∫ x : E, (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q) ∂μ) :=
      Real.sqrt_le_sqrt he
    _ = B * Real.sqrt (∫ x : E, (1 + ‖x‖ ^ 2) ^ m * (ρ + ‖x‖) ^ (-2 * q) ∂μ) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (sqrt_integral_sobolevWeight_mul_radialDecay_le hρ hm hq) hB

end JanetCartan.Localization
