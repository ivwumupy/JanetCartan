module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SobolevIntegration

/-!
# Localization and the actual datum-wise strong integral

The noncomparable-frequency part of `app:ch_regular:eq:chain-tail` can use
identified per-time graph estimates. This deduction transfers exactly those
estimates through the bounded elapsed integral, its literal Hilbert adjoint,
and the strong regularization limit. It needs only L² orbit measurability.
The producers are `EvolutionLocalization` for the per-time estimates and
`EvolutionIntegral.KernelIdentification` for measurability and strong limits.

This does not estimate the interior joint stationary branch: protection of
zero-characteristic segments supplies no per-time arbitrary-energy graph
estimate. That branch must use the joint half-space argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open Pseudodifferential RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ} {Δ C₀ : ℝ}
variable {T : ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q}

/-- Physical localization commutes with the bounded strong integral in its
literal order. Integrability is derived from the producer's LOW graph bound,
not from the desired tail estimate (`app:ch_regular:eq:chain-tail`). -/
theorem localized_strongIntegral_apply
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀) (u : SpacetimeL2 d q) :
    (1 - Mo) (strongIntegral T Δ C₀ hmeas hbound (Mi u)) =
      ∫ r in Icc 0 Δ, (1 - Mo) (T r (Mi u)) := by
  rw [strongIntegral_apply]
  exact ((1 - Mo).integral_comp_comm
    (integrableOn_apply_of_uniform_bound hmeas hbound (Mi u))).symm

/-- Identified per-time L²-to-Hᵐ estimates pass to the localized actual
strong integral with the exact cost `Δ`. The input is the per-r graph
estimate, not an integrated estimate. This is used for noncomparable shells
or for regions separated from the FULL fixed-r graph
(`app:ch_regular:eq:chain-tail`). -/
theorem localized_strongIntegral_sobolev_bound
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (hΔ : 0 ≤ Δ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀) (m : ℕ) (B : ℝ)
    (hsob : ∀ r ∈ Icc 0 Δ, ∀ u : SpacetimeL2 d q,
      MemVectorFourierSobolev (m : ℝ) ((1 - Mo) (T r (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) (T r (Mi u))) ≤ B * ‖u‖)
    (u : SpacetimeL2 d q) :
    MemVectorFourierSobolev (m : ℝ)
        ((1 - Mo) (strongIntegral T Δ C₀ hmeas hbound (Mi u))) ∧
      vectorFourierSobolevNorm (m : ℝ)
        ((1 - Mo) (strongIntegral T Δ C₀ hmeas hbound (Mi u))) ≤ (Δ * B) * ‖u‖ := by
  rw [localized_strongIntegral_apply]
  have hi := (1 - Mo).integrable_comp
    (integrableOn_apply_of_uniform_bound hmeas hbound (Mi u))
  simpa only [mul_assoc] using
    SobolevIntegration.integral_vectorSobolev_bound hΔ (m : ℝ) (B * ‖u‖)
      (fun r ↦ (1 - Mo) (T r (Mi u))) hi (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact hsob r hr u)

/-- Localizing the literal adjoint does not alter its internal multiplier
order. Only the actual Hilbert adjoint family appears under the integral
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem localized_strongIntegral_adjoint_apply
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (hmeasAdj : ∀ u, AEStronglyMeasurable (fun r ↦ (T r).adjoint u)
      (volume.restrict (Icc 0 Δ))) (u : SpacetimeL2 d q) :
    (1 - Mo) ((strongIntegral T Δ C₀ hmeas hbound).adjoint (Mi u)) =
      ∫ r in Icc 0 Δ, (1 - Mo) ((T r).adjoint (Mi u)) := by
  have hba : ∀ r ∈ Icc 0 Δ, ‖(T r).adjoint‖ ≤ C₀ := by
    intro r hr
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound r hr
  rw [strongIntegral_adjoint_apply hmeas hbound hmeasAdj]
  exact ((1 - Mo).integral_comp_comm
    (integrableOn_apply_of_uniform_bound hmeasAdj hba (Mi u))).symm

/-- The identified reversed graph bound passes to the localized literal
adjoint of the SAME elapsed strong integral. The low bound is inherited by
Hilbert adjunction; no new realization is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem localized_strongIntegral_adjoint_sobolev_bound
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q) (hΔ : 0 ≤ Δ)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (hmeasAdj : ∀ u, AEStronglyMeasurable (fun r ↦ (T r).adjoint u)
      (volume.restrict (Icc 0 Δ))) (m : ℕ) (B : ℝ)
    (hsob : ∀ r ∈ Icc 0 Δ, ∀ u : SpacetimeL2 d q,
      MemVectorFourierSobolev (m : ℝ) ((1 - Mo) ((T r).adjoint (Mi u))) ∧
        vectorFourierSobolevNorm (m : ℝ) ((1 - Mo) ((T r).adjoint (Mi u))) ≤ B * ‖u‖)
    (u : SpacetimeL2 d q) :
    MemVectorFourierSobolev (m : ℝ)
        ((1 - Mo) ((strongIntegral T Δ C₀ hmeas hbound).adjoint (Mi u))) ∧
      vectorFourierSobolevNorm (m : ℝ)
        ((1 - Mo) ((strongIntegral T Δ C₀ hmeas hbound).adjoint (Mi u))) ≤ (Δ * B) * ‖u‖ := by
  have hba : ∀ r ∈ Icc 0 Δ, ‖(T r).adjoint‖ ≤ C₀ := by
    intro r hr
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound r hr
  rw [localized_strongIntegral_adjoint_apply Mi Mo hmeas hbound hmeasAdj]
  simpa only [localized_strongIntegral_apply] using
    localized_strongIntegral_sobolev_bound Mi Mo hΔ hmeasAdj hba m B hsob u

/-- The original low-bounded strong graph regularizations commute with
elapsed integration and both outside localizers. The limit is the actual
strong integral, not an unspecified extension of the kernel
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem tendsto_localized_regularized_strongIntegral
    (Mi Mo : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hmeas : ∀ u, AEStronglyMeasurable (fun r ↦ T r u) (volume.restrict (Icc 0 Δ)))
    (hbound : ∀ r ∈ Icc 0 Δ, ‖T r‖ ≤ C₀)
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hmeasReg : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u)
      (volume.restrict (Icc 0 Δ)))
    (hboundReg : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C₀)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop (𝓝 (T r u)))
    (u : SpacetimeL2 d q) :
    Tendsto (fun j ↦ ∫ r in Icc 0 Δ, (1 - Mo) (Treg j r (Mi u))) atTop
      (𝓝 ((1 - Mo) (strongIntegral T Δ C₀ hmeas hbound (Mi u)))) := by
  have h := (1 - Mo).continuous.continuousAt.tendsto.comp
    (tendsto_integral_apply_of_uniform_bound Treg hmeasReg hboundReg hlim (Mi u))
  have he (j : ℕ) : (∫ r in Icc 0 Δ, (1 - Mo) (Treg j r (Mi u))) =
      (1 - Mo) (∫ r in Icc 0 Δ, Treg j r (Mi u)) :=
    (1 - Mo).integral_comp_comm
      (integrableOn_apply_of_uniform_bound (hmeasReg j) (hboundReg j) (Mi u))
  simp only [he, strongIntegral_apply]
  simp only [Function.comp_def] at h
  convert! h using 1

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
