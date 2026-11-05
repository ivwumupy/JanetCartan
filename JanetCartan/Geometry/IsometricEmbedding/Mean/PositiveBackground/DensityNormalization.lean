module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Synthesis
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.Synthesis

/-!
# Factor-four density and the existing multiplier output

The literal `4 Re` radian synthesis of `app:ch_background:eq:bg-density-four`
is identified with the density multiplier's `2 Re` unitary output. Its exact
conversion is `2 * synthesisFactor n`. This connection lets the positive
background use the proved physical Sobolev estimates without changing the
Fourier convention or inserting a cutoff in initial position.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.PositiveBackground

open ContinuumRow CarrierSobolev RawCutoffBounds UncutDensity ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- Exact normalization of factor-four synthesis in terms of the actual
unitary multiplier output (`app:ch_background:eq:bg-density-four`). -/
theorem realSynthesisL2_four_eq_densityUncutL2
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρm : Measurable ρ) (hχm : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z η, ‖η‖ = 1 → ‖ρ (z, η)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    realSynthesisL2 4 (densityFrequencyOutput 0 hρm hχm hM hρ hχ hχ0 f hf) =
      (2 * synthesisFactor n) • densityUncutL2 hρm hχm hM hρ hχ hχ0 f hf := by
  apply Lp.ext
  let u := densitySynthesisL2 hρm hχm hM hρ hχ hχ0 f hf
  filter_upwards [Lp.coeFn_smul (4 * synthesisFactor n)
      (Complex.reCLM.compLpL 2 (carrierMeasure n) u),
    Complex.reCLM.coeFn_compLpL (p := 2) u,
    Lp.coeFn_smul (2 * synthesisFactor n) (densityUncutL2 hρm hχm hM hρ hχ hχ0 f hf),
    densityUncutL2_coeFn hρm hχm hM hρ hχ hχ0 f hf] with p hleft hre hright htwo
  change ((4 * synthesisFactor n) • Complex.reCLM.compLpL 2 (carrierMeasure n) u) p = _
  rw [hleft, hright, Pi.smul_apply, Pi.smul_apply, hre, htwo]
  change (4 * synthesisFactor n) * (u p).re = (2 * synthesisFactor n) * (2 * (u p).re)
  ring

/-- The multiplier's real L² output, rescaled by the exact constant, has
literal factor-four synthesis as its representative. The regular raw input
supplies integrable slices (`app:ch_background:eq:bg-density-four`). -/
theorem densityUncutL2_four_coeFn (d : CarrierData n N) (s : ℕ)
    (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ z η, |d.angularCutoff z η| ≤ M)
    (hhi : ∀ r, |d.highCutoff r| ≤ 1) (hhi0 : d.highCutoff 0 = 0)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f)
    (hf1 : CarrierWeightedMem (etaBesselWeight 1) f) :
    (2 * synthesisFactor n) • densityUncutL2 hρm hhm hM
      (fun z η _ ↦ by simpa using hρ z η) hhi hhi0 f hf1 =ᵐ[carrierMeasure n]
      initialDensity d 4 f := by
  obtain ⟨hg, heq⟩ := realSynthesisL2_raw_coeFn d s hs hρm hhm hM
    (by norm_num : (0 : ℝ) ≤ 1) hρ hhi 4 f hf
  have hfreq : densityFrequencyOutput 0 hρm hhm hM
      (fun z η _ ↦ by simpa using hρ z η) hhi hhi0 f hf1 = hg.toLp _ := by
    apply Lp.ext
    filter_upwards [densityFrequencyOutput_coeFn 0 hρm hhm hM
      (fun z η _ ↦ by simpa using hρ z η) hhi hhi0 f hf1, hg.coeFn_toLp] with p hp hgp
    rw [hp, hgp]
    simp only [etaBesselWeight, pow_zero, one_smul]
    rfl
  rw [← hfreq, realSynthesisL2_four_eq_densityUncutL2] at heq
  exact heq

end JanetCartan.PositiveBackground
