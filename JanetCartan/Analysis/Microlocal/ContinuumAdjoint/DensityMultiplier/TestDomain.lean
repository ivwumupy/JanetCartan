module
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.CompactMasks
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
/-!
# Compact smooth tests for the density multiplier

The exact unbounded-frequency symbol in `app:ch_background:eq:bg-density-adjoint`
preserves compact smooth tests because its low cutoff removes the singularity
at zero. All weighted carrier jet energies of these tests are finite on the
literal product Lebesgue measure. This supplies the test domain to the multiplier
estimate, without imposing any frequency ceiling on the operator itself.

Density of these tests in the shared mixed weak graph norm and the partial
inverse Fourier identification are separate obligations of `Mean/CarrierSobolev`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n : ℕ}

/-- The low cutoff removes both the angular singularity and the square-root
singularity at zero. The literal half-order density symbol is smooth
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem contDiff_densityFrequencySymbol {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ)
    (hlow : ∀ r ≤ 1, χ r = 0) : ContDiff ℝ ∞ (densityFrequencySymbol ρ χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x.2 = 0
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have he : ∀ᶠ y : CarrierVariable n in nhds x, ‖y.2‖ < 1 :=
      continuous_snd.norm.continuousAt.eventually_lt continuousAt_const (by simp [hx])
    filter_upwards [he] with y hy
    exact densityFrequencySymbol_eq_zero_of_low ρ hlow y hy.le
  · have hn : ContDiffAt ℝ ∞ (fun y : CarrierVariable n ↦ ‖y.2‖) x :=
      contDiffAt_snd.norm ℝ hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (hn.sqrt (norm_ne_zero_iff.mpr hx))).mul
      (contDiff_angularHighMask hρ hχ hlow).contDiffAt

/-- Carrier derivatives and transverse weights preserve the compact support
of a smooth test. This is a support statement about the datum, not an upper
frequency cutoff on the density multiplier (`app:ch_background:eq:bg-density-adjoint`). -/
theorem hasCompactSupport_weightedCarrierJet (k t : ℕ) {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    HasCompactSupport (weightedCarrierJet k t f) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hn
  have hz : iteratedFDeriv ℝ k f x = 0 := by
    by_contra hne
    exact hn (support_iteratedFDeriv_subset k hne)
  have hzero : iteratedFDeriv ℝ k (fun z ↦ f (z, x.2)) x.1 = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hz] using norm_carrierJet_le_fullJet k hf x) (norm_nonneg _)
  exact hx (by simp [weightedCarrierJet, hzero])

/-- Every mixed weighted carrier jet of a compact smooth test has finite
Lebesgue L² energy (`app:ch_background:eq:bg-density-adjoint`). -/
theorem memLp_weightedCarrierJet_of_compactSupport (k t : ℕ) {f : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    MemLp (weightedCarrierJet k t f) 2 (carrierMeasure n) := by
  have : IsFiniteMeasureOnCompacts (carrierMeasure n) := by
    unfold carrierMeasure
    infer_instance
  exact (continuous_weightedCarrierJet k t hf).memLp_of_hasCompactSupport
    (hasCompactSupport_weightedCarrierJet k t hf hc)

/-- The actual density symbol preserves the compact smooth test domain.
The operator itself still has unbounded frequency support
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densitySymbol_mul_preserves_tests {ρ f : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun x ↦ densityFrequencySymbol ρ χ x * f x) ∧
      HasCompactSupport (fun x ↦ densityFrequencySymbol ρ χ x * f x) :=
  ⟨(contDiff_densityFrequencySymbol hρ hχ hlow).mul hf, hc.mul_left⟩

/-- Uniform bounds on genuine compact smooth tests follow from the fixed
mask alone. All input and output integrability obligations are discharged;
no finite-energy hypothesis or desired multiplier estimate is assumed
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbol_test_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ s, ∀ t : ℕ, ∀ f : CarrierVariable n → ℂ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      MemLp (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
          2 (carrierMeasure n) ∧
        lpNorm (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
          2 (carrierMeasure n) ≤
        ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * C) *
          lpNorm (weightedCarrierJet (k - i) (t + 1) f) 2 (carrierMeasure n) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_densitySymbol_jet_bound_of_compactSupport s hρ hcρ hχsmooth hlow hχ
  exact ⟨C, hC, fun k hk t f hf hc ↦ hbound k hk t f hf
    (fun j _ ↦ memLp_weightedCarrierJet_of_compactSupport j (t + 1) hf hc)⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
