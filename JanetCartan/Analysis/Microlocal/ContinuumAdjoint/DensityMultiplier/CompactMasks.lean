module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.PhysicalCutoff

/-!
# Uniform density multiplier estimates for fixed compact masks

Compact support and smoothness produce all mask derivative constants used in
`app:ch_background:eq:bg-density-adjoint`. The frequency estimate retains the
literal half-order symbol on the entire frequency space. The physical estimate
includes every carrier and initial derivative of the cutoff. The constants are
chosen before the datum, and no multiplier estimate is assumed as input.

These are smooth-data estimates. Their identification with the shared mixed
weak graph norm and the partial inverse Fourier map remains a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n : ℕ}

/-- A fixed smooth compact angular extension has bounded carrier derivatives
of all prescribed orders, uniformly on unit directions. This discharges the
mask-bound input to the carrier Leibniz estimate
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_bound_carrierJets_of_compactSupport (s : ℕ)
    {ρ : CarrierVariable n → ℂ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ s, ∀ z θ, ‖θ‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun w ↦ ρ (w, θ)) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hc.exists_bound_iteratedFDeriv hρ s
  exact ⟨C, hC, fun i hi z θ _ ↦
    (norm_carrierJet_le_fullJet i hρ (z, θ)).trans (hbound i hi (z, θ))⟩

/-- The actual full-frequency mixed-jet estimate with constants produced from
the fixed compact mask. Finite input jet energies are the only assumptions on
the datum; the output membership is a conclusion
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbol_jet_bound_of_compactSupport (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ s, ∀ t : ℕ, ∀ f : CarrierVariable n → ℂ,
      ContDiff ℝ ∞ f →
      (∀ j ≤ k, MemLp (weightedCarrierJet j (t + 1) f) 2 (carrierMeasure n)) →
      MemLp (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
          2 (carrierMeasure n) ∧
        lpNorm (weightedCarrierJet k t (fun x ↦ densityFrequencySymbol ρ χ x * f x))
          2 (carrierMeasure n) ≤
        ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * C) *
          lpNorm (weightedCarrierJet (k - i) (t + 1) f) 2 (carrierMeasure n) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_carrierJets_of_compactSupport s hρ hc
  refine ⟨C, hC, ?_⟩
  intro k hk t f hf hmem
  exact weightedCarrierJet_densitySymbol_memLp_and_bound k t hρ hf hχsmooth hlow hχ
    (fun _ ↦ C) (fun _ _ ↦ hC) (fun i hi ↦ hbound i (hi.trans hk)) hmem

/-- A fixed compact physical cutoff supplies all derivative constants for the
full `(z,y)` Leibniz bound, including the factor two from the real density.
The constant is independent of the physical datum
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densityPhysicalCutoff_jet_bound_of_compactSupport (s : ℕ)
    {χ : CarrierVariable n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ s, ∀ u : CarrierVariable n → ℂ,
      ContDiff ℝ ∞ u →
      (∀ j ≤ k, MemLp (iteratedFDeriv ℝ j u) 2 (carrierMeasure n)) →
      MemLp (iteratedFDeriv ℝ k (densityPhysicalCutoff χ u)) 2 (carrierMeasure n) ∧
        lpNorm (iteratedFDeriv ℝ k (densityPhysicalCutoff χ u)) 2 (carrierMeasure n) ≤
        ∑ i ∈ Finset.range (k + 1), (2 * (k.choose i : ℝ) * C) *
          lpNorm (iteratedFDeriv ℝ (k - i) u) 2 (carrierMeasure n) := by
  obtain ⟨C, hC, hbound⟩ := hc.exists_bound_iteratedFDeriv hχ s
  refine ⟨C, hC, ?_⟩
  intro k hk u hu hmem
  exact densityPhysicalCutoff_jet_memLp_and_bound k hχ hu (fun _ ↦ C)
    (fun _ _ ↦ hC) (fun i hi ↦ hbound i (hi.trans hk)) hmem

end JanetCartan.ContinuumAdjoint.DensityMultiplier
