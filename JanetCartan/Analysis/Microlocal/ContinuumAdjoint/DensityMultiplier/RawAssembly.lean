module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputApproximation
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.SobolevAssembly

/-!
# Raw-norm assembly of the density multiplier

This is the final multiplier composition for
`app:ch_background:eq:bg-density-adjoint`. The input graph
approximation, output graph closure, partial inverse Fourier transfer, and
physical cutoff are instantiated by their checked producers.

The first theorem isolates the two test-space inputs. The final theorem
discharges them with `denseRange_rawTestSobolev` and
`exists_mixedCarrierJetNorm_le_rawTestSobolev`, proving the full
`X^(s+1) → H^s` estimate for the actual density, before and after cutoff.
Only the fixed masks' stated smoothness, support and size conditions remain.
The initial-adjoint consumer must separately supply the raw regularity of
its canonical input; no canonical inverse estimate is assumed or proved here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds CarrierSobolev
variable {n : ℕ}

/-- Once the two raw test-space inputs are proved, the actual full-frequency
density satisfies the required one-integer-derivative estimate, both before
and after the physical cutoff. Every downstream analytic premise is
discharged by the earlier constructions. Density and reverse comparison are
explicit remaining obligations, not assertions of this theorem
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densityOutputs_rawSobolev_bound_of_test_inputs (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (hρsmooth : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    {χy : CarrierVariable n → ℝ} (hχy : ContDiff ℝ ∞ χy) (hcy : HasCompactSupport χy)
    (hdense : DenseRange (rawTestSobolev (n := n) (s + 1)))
    {C : ℝ} (hC : 0 ≤ C)
    (hcompare : ∀ f : carrierInitialTestSpace n,
      mixedCarrierJetNorm (s + 1) f.val ≤ C * ‖rawTestSobolev (s + 1) f‖) :
    let m := (hχy.continuous.memLp_top_of_hasCompactSupport hcy (carrierMeasure n)).toLp χy
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : CarrierL2 n) (hu : MemRawSobolev (s + 1) u),
      let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu.mono (by omega : 1 ≤ s + 1))
      (MemPhysicalSobolev s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hw) ∧
        physicalSobolevNorm s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hw) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hw)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hw)) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hw)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hw)) ≤
          L * rawSobolevNorm (s + 1) u) := by
  obtain ⟨B, hB, hb⟩ := exists_densityOutputs_sobolev_bound_of_approximation
    hρmeas hχmeas hM hρ hχ hχ0 s hρsmooth hcρ hχsmooth hlow hχy hcy
  refine ⟨B * C, mul_nonneg hB hC, fun u hu ↦ ?_⟩
  obtain ⟨f, A, hf, hfu, hA, hbound⟩ := exists_mixedCarrierJet_approximation_of_denseRange
    (s + 1) hdense hC hcompare (RawSobolevSpace.ofRawL2 (s + 1) u hu)
  simp only [RawSobolevSpace.toRawL2_ofRawL2] at hfu
  rw [RawSobolevSpace.norm_eq, RawSobolevSpace.toRawL2_ofRawL2] at hbound
  have hout := hb f u
    (carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu.mono (by omega : 1 ≤ s + 1)))
    A hf hfu hA
  have hfinal : B * A ≤ (B * C) * rawSobolevNorm (s + 1) u := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hbound hB
  exact ⟨⟨hout.1.1, hout.1.2.trans hfinal⟩,
    ⟨hout.2.1.1, hout.2.1.2.trans hfinal⟩, ⟨hout.2.2.1, hout.2.2.2.trans hfinal⟩⟩

/-- The exact full-frequency half-order density multiplier maps the shared
raw `X^(s+1)` domain into physical `H^s`, with one constant for complex
synthesis, twice its real part, and the physically cut real density.
Compact frequency-side density and the reverse input comparison are proved
and instantiated here; no approximation, output regularity, or norm estimate
is an analytic premise. This supplies the multiplier step of
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` to the initial-adjoint consumer.
All carrier and initial coordinates and the unitary radian normalization
are those of the existing raw and physical spaces. -/
theorem exists_densityOutputs_rawSobolev_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
    (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)
    (hρsmooth : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    {χy : CarrierVariable n → ℝ} (hχy : ContDiff ℝ ∞ χy) (hcy : HasCompactSupport χy) :
    let m := (hχy.continuous.memLp_top_of_hasCompactSupport hcy (carrierMeasure n)).toLp χy
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : CarrierL2 n) (hu : MemRawSobolev (s + 1) u),
      let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu.mono (by omega : 1 ≤ s + 1))
      (MemPhysicalSobolev s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hw) ∧
        physicalSobolevNorm s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hw) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hw)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hw)) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hw)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hw)) ≤
          L * rawSobolevNorm (s + 1) u) := by
  obtain ⟨C, hC, hcompare⟩ := exists_mixedCarrierJetNorm_le_rawTestSobolev (n := n) (s + 1)
  exact exists_densityOutputs_rawSobolev_bound_of_test_inputs s
    hρmeas hχmeas hM hρ hχ hχ0 hρsmooth hcρ hχsmooth hlow hχy hcy
    (denseRange_rawTestSobolev (s + 1)) hC hcompare

/-- Fixed smooth compact angular and physical masks yield the full density
bound at every integer order, with the angular size bound produced from compact
support before the order and datum are chosen. Measurability and vanishing at
zero are also discharged here. The only cutoff size condition is the usual
`|χ_hi| ≤ 1`; the high-frequency plateau is not needed for this bound, and
`densityFrequencySymbol_eq_of_high` retains it in the literal symbol whenever
present. This is the fixed-mask input to
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_densityOutputs_rawSobolev_bounds_of_compactMasks
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρsmooth : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1)
    {χy : CarrierVariable n → ℝ} (hχy : ContDiff ℝ ∞ χy) (hcy : HasCompactSupport χy) :
    ∃ (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M), ∀ s : ℕ,
      let m := (hχy.continuous.memLp_top_of_hasCompactSupport hcy (carrierMeasure n)).toLp χy
      ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : CarrierL2 n) (hu : MemRawSobolev (s + 1) u),
        let hw := carrierWeightedMem_etaBesselWeight_of_rawSobolev (hu.mono (by omega : 1 ≤ s + 1))
        (MemPhysicalSobolev s (densitySynthesisL2
            hρsmooth.continuous.measurable hχsmooth.continuous.measurable
            hM hρ hχ (hlow 0 zero_le_one) u hw) ∧
          physicalSobolevNorm s (densitySynthesisL2
            hρsmooth.continuous.measurable hχsmooth.continuous.measurable
            hM hρ hχ (hlow 0 zero_le_one) u hw) ≤
            L * rawSobolevNorm (s + 1) u) ∧
        (MemPhysicalSobolev s
            (physicalComplexifyL2 (densityUncutL2
              hρsmooth.continuous.measurable hχsmooth.continuous.measurable
              hM hρ hχ (hlow 0 zero_le_one) u hw)) ∧
          physicalSobolevNorm s
            (physicalComplexifyL2 (densityUncutL2
              hρsmooth.continuous.measurable hχsmooth.continuous.measurable
              hM hρ hχ (hlow 0 zero_le_one) u hw)) ≤
            L * rawSobolevNorm (s + 1) u) ∧
        (MemPhysicalSobolev s
            (physicalComplexifyL2 (densityOutputL2
              hρsmooth.continuous.measurable hχsmooth.continuous.measurable
              hM hρ hχ (hlow 0 zero_le_one) m u hw)) ∧
          physicalSobolevNorm s
            (physicalComplexifyL2 (densityOutputL2
              hρsmooth.continuous.measurable hχsmooth.continuous.measurable
              hM hρ hχ (hlow 0 zero_le_one) m u hw)) ≤
            L * rawSobolevNorm (s + 1) u) := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_carrierJets_of_compactSupport 0 hρsmooth hcρ
  have hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M := by
    intro z θ hθ
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 le_rfl z θ hθ
  exact ⟨M, hM, hρ, fun s ↦ exists_densityOutputs_rawSobolev_bound s
    hρsmooth.continuous.measurable hχsmooth.continuous.measurable
    hM hρ hχ (hlow 0 zero_le_one) hρsmooth hcρ hχsmooth hlow hχy hcy⟩

end JanetCartan.ContinuumAdjoint.DensityMultiplier
