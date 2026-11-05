module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.MixedJetClosure
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization

/-!
# Actual full-frequency density synthesis

Compose the literal half-order multiplier with the shared partial unitary
radian inverse and the actual real physical output operators. This constructs
`D` on the existing weighted carrier L² domain, without frequency truncation.
The compact test formula retains the precise inverse Fourier normalization.
The order-zero bounds follow from the weighted multiplier estimate and
Plancherel. Higher orders still require the shared raw mixed-Sobolev transfer;
this file does not identify transverse moments alone with that scale.

The consumer is the initial-adjoint assembly for
`app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds CarrierSobolev
variable {n : ℕ}

/-- All transverse weighted input conditions hold on the shared compact
smooth test domain. This supplies the test input to the literal synthesis
formula, without any additional analytic premise
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem carrierInitialTest_weightedMem (s : ℕ) (f : carrierInitialTestSpace n) :
    CarrierWeightedMem (etaBesselWeight s) (carrierInitialTestToLp f) :=
  carrierWeightedMem_of_zeroJet s (carrierInitialTestToLp f)
    (carrierInitialTest_memLp f).coeFn_toLp
    (memLp_weightedCarrierJet_of_compactSupport 0 s f.property.1 f.property.2)

section FixedMask
variable {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
  (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
  {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
  (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)

/-- The complex initial-variable synthesis of the exact unbounded half-order
symbol, before real quadrature and physical cutoff
(`app:ch_background:eq:bg-density-adjoint`). -/
def densitySynthesisL2 (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) : CarrierL2 n :=
  partialUnitaryInverse n (densityFrequencyOutput 0 hρmeas hχmeas hM hρ hχ hχ0 f hf)

/-- The actual real density before the physical cutoff, on the existing
weighted carrier classes (`app:ch_background:eq:bg-density-adjoint`). -/
def densityUncutL2 (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) : Lp ℝ 2 (carrierMeasure n) :=
  twoReL2 (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f hf)

/-- The full physical density with the fixed physical mask, on literal
Lebesgue classes (`app:ch_background:eq:bg-density-adjoint`). -/
def densityOutputL2 (m : Lp ℝ ∞ (carrierMeasure n)) (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) : Lp ℝ 2 (carrierMeasure n) :=
  densityPhysicalCutoffL2 m (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f hf)

/-- Plancherel gives the complex synthesis estimate with exactly the same
constant as the frequency multiplier (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densitySynthesisL2_le (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    ‖densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f hf‖ ≤
      M * carrierWeightedNorm (etaBesselWeight 1) f hf := by
  rw [densitySynthesisL2, partialUnitaryInverse_norm]
  exact norm_densityFrequencyOutput_le 0 hρmeas hχmeas hM hρ hχ hχ0 f hf

/-- Before the physical cutoff, the exact factor two is the only additional
L² cost (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityUncutL2_le (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    ‖densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 f hf‖ ≤
      (2 * M) * carrierWeightedNorm (etaBesselWeight 1) f hf := by
  exact (norm_twoReL2_le _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (norm_densitySynthesisL2_le hρmeas hχmeas hM hρ hχ hχ0 f hf) (by norm_num : (0 : ℝ) ≤ 2))

/-- The physical mask bound and actual partial Plancherel prove the full
order-zero density estimate, without assuming any output bound
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_densityOutputL2_le (m : Lp ℝ ∞ (carrierMeasure n))
    {B : ℝ} (hB : 0 ≤ B) (hm : ∀ᵐ x ∂carrierMeasure n, |m x| ≤ B)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    ‖densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m f hf‖ ≤
      (2 * B * M) * carrierWeightedNorm (etaBesselWeight 1) f hf := by
  exact (norm_densityPhysicalCutoffL2_le m hm _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (norm_densitySynthesisL2_le hρmeas hχmeas hM hρ hχ hχ0 f hf)
      (mul_nonneg (by norm_num) hB))

/-- The real density is literally twice the real part of the synthesized
class, including its factor two (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityUncutL2_coeFn (f : CarrierL2 n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 f hf =ᵐ[carrierMeasure n]
      fun x ↦ 2 * (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f hf x).re :=
  twoReL2_coeFn _

/-- The physical output uses the original physical variables and the actual
mask operator (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityOutputL2_coeFn (m : Lp ℝ ∞ (carrierMeasure n))
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight 1) f) :
    densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m f hf =ᵐ[carrierMeasure n]
      densityPhysicalCutoff m (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 f hf) :=
  densityPhysicalCutoffL2_coeFn _ _

/-- On compact smooth tests, the constructed synthesis agrees with the
literal partial inverse integral. Its prefactor is `synthesisFactor n` inverse,
i.e. `(2π)^(-(n-1)/2)`; no extra frequency-dependent factor occurs
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densitySynthesisL2_test_coeFn
    (hρsmooth : ContDiff ℝ ∞ ρ) (hχsmooth : ContDiff ℝ ∞ χ)
    (hlow : ∀ r ≤ 1, χ r = 0) (f : carrierInitialTestSpace n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) (carrierInitialTestToLp f)) :
    densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 (carrierInitialTestToLp f) hf
      =ᵐ[carrierMeasure n] fun x ↦ unitaryInverseIntegral
        (fun η ↦ densityFrequencySymbol ρ χ (x.1, η) * f.val (x.1, η)) x.2 := by
  let g := densitySymbolTestMap hρsmooth hχsmooth hlow f
  have he : densityFrequencyOutput 0 hρmeas hχmeas hM hρ hχ hχ0
      (carrierInitialTestToLp f) hf = carrierInitialTestToLp g := by
    apply Lp.ext
    filter_upwards [densityFrequencyOutput_coeFn 0 hρmeas hχmeas hM hρ hχ hχ0
      (carrierInitialTestToLp f) hf, (carrierInitialTest_memLp f).coeFn_toLp,
      (carrierInitialTest_memLp g).coeFn_toLp] with x hx hy hz
    change carrierInitialTestToLp f x = f.val x at hy
    change carrierInitialTestToLp g x = g.val x at hz
    rw [hx, hz, hy]
    simp only [etaBesselWeight, pow_zero, one_smul]
    rfl
  rw [densitySynthesisL2, he]
  exact partialUnitaryInverse_compact_test_ae g.property.1.continuous g.property.2

/-- The compact-test formula for the full real density includes the physical
mask, literal half-order symbol, and exact unitary inverse integral
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityOutputL2_test_coeFn
    (hρsmooth : ContDiff ℝ ∞ ρ) (hχsmooth : ContDiff ℝ ∞ χ)
    (hlow : ∀ r ≤ 1, χ r = 0) (m : Lp ℝ ∞ (carrierMeasure n))
    (f : carrierInitialTestSpace n)
    (hf : CarrierWeightedMem (etaBesselWeight 1) (carrierInitialTestToLp f)) :
    densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m (carrierInitialTestToLp f) hf
      =ᵐ[carrierMeasure n] fun x ↦ 2 * (m x • unitaryInverseIntegral
        (fun η ↦ densityFrequencySymbol ρ χ (x.1, η) * f.val (x.1, η)) x.2).re := by
  filter_upwards [densityOutputL2_coeFn hρmeas hχmeas hM hρ hχ hχ0 m
    (carrierInitialTestToLp f) hf,
    densitySynthesisL2_test_coeFn hρmeas hχmeas hM hρ hχ hχ0
      hρsmooth hχsmooth hlow f hf] with x hx hy
  rw [hx, densityPhysicalCutoff, hy]

end FixedMask
end JanetCartan.ContinuumAdjoint.DensityMultiplier
