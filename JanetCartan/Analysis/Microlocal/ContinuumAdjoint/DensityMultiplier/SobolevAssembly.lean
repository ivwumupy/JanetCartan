module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.RawBounds

/-!
# Sobolev bounds for the actual density output from input graph approximation

The output construction in `app:ch_background:eq:bg-density-adjoint` now
composes the proved unbounded multiplier estimate, mixed-jet closure, partial
Plancherel transfer, and all-coordinate physical cutoff estimate. The result
concerns exactly `densitySynthesisL2`, `densityUncutL2`, and `densityOutputL2`;
the graph limit is identified with these existing operators.

Only input approximation remains conditional: compact smooth raw tests must
converge in L², be Cauchy in total mixed jets, and have convergent mixed norms.
The final raw-scale assembly must construct this approximation and bound its
limiting norm by the shared full raw Sobolev norm. No output regularity or
output norm estimate is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology ENNReal

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow RawCutoffBounds CarrierSobolev
variable {n : ℕ}

section FixedMask
variable {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
  (hρmeas : Measurable ρ) (hχmeas : Measurable χ)
  {M : ℝ} (hM : 0 ≤ M) (hρ : ∀ z θ, ‖θ‖ = 1 → ‖ρ (z, θ)‖ ≤ M)
  (hχ : ∀ r, |χ r| ≤ 1) (hχ0 : χ 0 = 0)

/-- Uniqueness of the actual full-frequency multiplier class identifies the
closed-graph output with the existing synthesis input
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityFrequencyOutput_zero_eq_of_ae (u v : CarrierL2 n)
    (hu : CarrierWeightedMem (etaBesselWeight 1) u)
    (hv : v =ᵐ[carrierMeasure n] fun x ↦ densityFrequencySymbol ρ χ x * u x) :
    densityFrequencyOutput 0 hρmeas hχmeas hM hρ hχ hχ0 u hu = v := by
  apply Lp.ext
  filter_upwards [densityFrequencyOutput_coeFn 0 hρmeas hχmeas hM hρ hχ hχ0 u hu, hv]
    with x hx hy
  simpa only [etaBesselWeight, pow_zero, one_smul, hy] using hx

/-- The constructed complex density synthesis has the full Sobolev bound
from input graph approximation. The output jets, their weak identities, and
their partial Plancherel estimate are all proved; only the input approximation
and its limiting numerical norm remain to be supplied by the raw-scale
assembly (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySynthesisL2_sobolev_bound_of_approximation (s : ℕ)
    (hρsmooth : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℕ → carrierInitialTestSpace n) (u : CarrierL2 n)
      (hu : CarrierWeightedMem (etaBesselWeight 1) u) (A : ℝ),
      (∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε) →
      Tendsto (fun j ↦ carrierInitialTestToLp (f j)) atTop (𝓝 u) →
      Tendsto (fun j ↦ mixedCarrierJetNorm (s + 1) (f j).val) atTop (𝓝 A) →
      MemPhysicalSobolev s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hu) ∧
        physicalSobolevNorm s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hu) ≤
          L * A := by
  obtain ⟨B, hB, hb⟩ := exists_densitySymbol_weakGraph_bound s hρsmooth hcρ hχsmooth hlow hχ
  obtain ⟨C, hC, hc⟩ := exists_partialUnitaryInverse_sobolev_bound_of_tendsto (n := n) s
  refine ⟨C * B, mul_nonneg hC hB, fun f u hu A hf hfu hA ↦ ?_⟩
  obtain ⟨v, J, he, hv, hJ, _, hbound⟩ := hb f u A hf hfu hA
  obtain ⟨hm, hn⟩ := hc (fun j ↦ densitySymbolTestMap hρsmooth hχsmooth hlow (f j))
    v J hv hJ
  rw [densitySynthesisL2, densityFrequencyOutput_zero_eq_of_ae
    hρmeas hχmeas hM hρ hχ hχ0 u v hu he]
  refine ⟨hm, hn.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hC

/-- The same fixed constant controls the complex synthesis, the uncut real
density, and the density after the physical cutoff. All real outputs are
literally complexified in the shared physical Sobolev scale. This completes
the output side of `app:ch_background:eq:bg-density-adjoint`; the stated
input approximation must still be instantiated from the full raw domain. -/
theorem exists_densityOutputs_sobolev_bound_of_approximation (s : ℕ)
    (hρsmooth : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    {χy : CarrierVariable n → ℝ} (hχy : ContDiff ℝ ∞ χy) (hcy : HasCompactSupport χy) :
    let m := (hχy.continuous.memLp_top_of_hasCompactSupport hcy (carrierMeasure n)).toLp χy
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℕ → carrierInitialTestSpace n) (u : CarrierL2 n)
      (hu : CarrierWeightedMem (etaBesselWeight 1) u) (A : ℝ),
      (∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε) →
      Tendsto (fun j ↦ carrierInitialTestToLp (f j)) atTop (𝓝 u) →
      Tendsto (fun j ↦ mixedCarrierJetNorm (s + 1) (f j).val) atTop (𝓝 A) →
      (MemPhysicalSobolev s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hu) ∧
        physicalSobolevNorm s (densitySynthesisL2 hρmeas hχmeas hM hρ hχ hχ0 u hu) ≤ L * A) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hu)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityUncutL2 hρmeas hχmeas hM hρ hχ hχ0 u hu)) ≤ L * A) ∧
      (MemPhysicalSobolev s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hu)) ∧
        physicalSobolevNorm s
          (physicalComplexifyL2 (densityOutputL2 hρmeas hχmeas hM hρ hχ hχ0 m u hu)) ≤ L * A) := by
  let m := (hχy.continuous.memLp_top_of_hasCompactSupport hcy (carrierMeasure n)).toLp χy
  obtain ⟨C, hC, hc⟩ := exists_densitySynthesisL2_sobolev_bound_of_approximation
    hρmeas hχmeas hM hρ hχ hχ0 s hρsmooth hcρ hχsmooth hlow
  obtain ⟨P, hP, hp⟩ := exists_densityPhysicalCutoffL2_sobolev_bound s χy hχy hcy
  let R := (4 * Real.pi) ^ s * 2 * (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨(1 + R + P) * C, by positivity, fun f u hu A hf hfu hA ↦ ?_⟩
  have hAnonneg : 0 ≤ A := ge_of_tendsto hA
    (Eventually.of_forall fun j ↦ mixedCarrierJetNorm_nonneg (s + 1) (f j).val)
  have hCA : 0 ≤ C * A := mul_nonneg hC hAnonneg
  obtain ⟨hm, hn⟩ := hc f u hu A hf hfu hA
  have hlarge (Q : ℝ) (hQ : Q ≤ 1 + R + P) :
      Q * (C * A) ≤ ((1 + R + P) * C) * A := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hQ hCA
  refine ⟨⟨hm, hn.trans ?_⟩, ⟨memPhysicalSobolev_complexTwoReL2 hm, ?_⟩,
    ⟨(hp _ hm).1, ?_⟩⟩
  · simpa only [one_mul] using hlarge 1 (by linarith)
  · exact (physicalSobolevNorm_complexTwoReL2_le hm).trans
      ((mul_le_mul_of_nonneg_left hn hR).trans (hlarge R (by linarith)))
  · exact (hp _ hm).2.trans
      ((mul_le_mul_of_nonneg_left hn hP).trans (hlarge P (by linarith)))

end FixedMask
end JanetCartan.ContinuumAdjoint.DensityMultiplier
