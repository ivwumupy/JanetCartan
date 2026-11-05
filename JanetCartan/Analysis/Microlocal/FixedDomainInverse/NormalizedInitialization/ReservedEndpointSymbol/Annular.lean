module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.FullSourceProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Calculus

/-!
# The annular selector preserves the endpoint's actual reserve

The original full-frequency endpoint is multiplied by the prescribed annular
selector. Every selector derivative is included. Its closed support gives a
fixed nonzero normalized carrier, and outside that support all jets vanish.
Both physical positions are exchanged for the literal Hilbert adjoint.
Consumer: the endpoint near-carrier estimate in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open RegularSector RegularSector.FinitePdo RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open ResidualLocalization ResponseTransfer ResponseTransfer.NearCarrierAssembly
open ResponseTransfer.NearCarrierFullLow FourierIntegral
open RawPrimary.AmplitudeGrades.Polynomial

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The actual annular endpoint and its exchanged adjoint have global
reserved normalized profiles from the original coefficient data and supplied
`W₁` certificate. No annular symbol bound or global coefficient extension is
assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_endpoint_reserved_annular_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (AQ AB : ℕ → ℝ) (cost : f.centers → ℕ → ℝ)
    (hAQ : ∀ m, 0 ≤ AQ m) (hAB : ∀ m, 0 ≤ AB m)
    (hcost : ∀ p m, 0 ≤ cost p m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (Rreserve Rcoeff : ℕ), Rreserve+10 ≤ Rcoeff →
      ∀ (L ρ : ℝ), 1 ≤ L → 1 ≤ ρ →
      ∀ Q : E → Fin (d+1) → MetricTensor (d+1), ContDiffOn ℝ ∞ Q Ω →
      ∀ B : E → MetricTensor (d+1),
      (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rcoeff)) →
      (∀ m, cNorm (closedBall x RQ) m B ≤ AB m * L ^ (m-Rcoeff)) →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p))) →
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ cost p m *
          (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p (backward : Bool),
      let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦ π (ρ⁻¹ • ξ) •
        orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W p)) y z ξ
      let α := normalizedFullAmplitude
        (ρ • if backward then exchangedAdjointAmplitude A else A) ρ
      ContDiff ℝ ∞ α ∧ ∀ k v,
        ‖iteratedFDeriv ℝ k α v‖ ≤ D k * L ^ (k-Rreserve) := by
  obtain ⟨C, hC, hb⟩ := exists_selected_endpoint_reserved_full_source_profiles
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
    (tsupport π) hcπ hzero AQ AB cost hAQ hAB hcost
  let X := fun k ↦ cNorm (tsupport π) k π
  have hX : ∀ k, 0 ≤ X k := fun k ↦ cNorm_nonneg _ _ _
  let sm : ℝ →L[ℝ] Mat →L[ℝ] Mat := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨productProfile sm X C, productProfile_nonneg sm hX hC, ?_⟩
  intro Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W J hW hbudget p backward A α
  let a := ρ • orientedMaskedPDOAmplitude false
    (endpointOutputMask f p output) (chartInputMask f p)
    (selectedEndpointSymbol f p threshold Q (W p))
  let g := normalizedFullAmplitude (if backward then exchangedAdjointAmplitude a else a) ρ
  obtain ⟨ha, hja, har, hjar⟩ := hb Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W hW hbudget p
  have hg : ContDiff ℝ ∞ g := by cases backward <;> assumption
  have hgj : ∀ k v, v.2.2 ∈ tsupport π →
      ‖iteratedFDeriv ℝ k g v‖ ≤ C k * L ^ (k-Rreserve) := by
    cases backward <;> assumption
  let pr : V →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp
    (ContinuousLinearMap.snd ℝ E (E × E))
  have hpr : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro v
    change ‖v.2.2‖ ≤ 1*‖v‖
    rw [one_mul]
    exact (norm_snd_le v.2).trans (norm_snd_le v)
  have hpj (k) (v : V) : ‖iteratedFDeriv ℝ k (π ∘ pr) v‖ ≤ X k := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr isOpen_univ
      hπ.contDiffOn (mem_univ _) k).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr)).trans
    by_cases hv : pr v ∈ tsupport π
    · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hcπ
        (fun z _ ↦ hπ.contDiffAt.of_le (by simp)) hv le_rfl
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh ↦ hv ((tsupport_iteratedFDeriv_subset k) hh)), norm_zero]
      exact hX k
  have hρne : ρ ≠ 0 := (zero_lt_one.trans_le hρ).ne'
  have he : α = fun v ↦ π (pr v) • g v := by
    cases backward <;> funext v <;>
      simp only [α, A, g, a, pr, normalizedFullAmplitude, exchangedAdjointAmplitude,
        orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, Pi.smul_apply,
        ContinuousLinearMap.comp_apply, inv_smul_smul₀ hρne,
        Matrix.conjTranspose_smul, star_trivial]
    all_goals exact smul_comm _ _ _
  rw [he]
  refine ⟨(hπ.comp pr.contDiff).smul hg, ?_⟩
  intro k v
  by_cases hv : pr v ∈ tsupport π
  · exact jet_bilinear_le sm isOpen_univ (hπ.comp pr.contDiff).contDiffOn
      hg.contDiffOn (mem_univ v) (b := Rreserve) hL hX hC
      (fun j ↦ (hpj j v).trans (le_mul_of_one_le_right (hX j) (one_le_pow₀ hL)))
      (fun j ↦ hgj j v hv) k
  · have hs : tsupport (fun v : V ↦ π (pr v) • g v) ⊆ pr ⁻¹' tsupport π :=
      (tsupport_smul_subset_left _ _).trans (tsupport_comp_subset_preimage π pr.continuous)
    rw [image_eq_zero_of_notMem_tsupport
      (fun hh ↦ hv (hs ((tsupport_iteratedFDeriv_subset k) hh))), norm_zero]
    exact mul_nonneg (productProfile_nonneg sm hX hC k) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
