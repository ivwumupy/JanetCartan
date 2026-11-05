module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.ForwardProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FullLow.Literal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks

/-!
# Original algebraic full amplitudes in both literal orientations

Conjugate transpose and exchange of the two physical positions are applied
to the entire masked amplitude. They preserve the forward profile and its
original coefficient reserve (`app:ch_response:eq:direct-envelope-profile`,
`app:ch_regular_base:eq:actual-matrix-inverse`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol

open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open FourierIntegral ResponseTransfer ResponseTransfer.NearCarrierFullLow

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Both literal orientations of the SAME selected algebraic full amplitude
have global smoothness and reserved joint profiles. The adjoint exchanges the
physical positions and conjugate-transposes the entire original mask/source
product. Separate original profiles of `Q` and `B` enter only through their
fixed maximum; neither field nor inverse is replaced
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_algebraic_full_source_reserved_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (p : f.centers) (o : Fin 2) (backward : Bool),
        let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦
          π (ρ⁻¹ • ξ) • orientedMaskedPDOAmplitude false
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B o) y z ξ
        let α : V → CMat := normalizedFullAmplitude
          (ρ • if backward then exchangedAdjointAmplitude A else A) ρ
        ContDiff ℝ ∞ α ∧ ∀ k v, ‖iteratedFDeriv ℝ k α v‖ ≤ C k * L ^ (k+1-Rstar) := by
  let Acoef := fun k ↦ max (AQ k) (AB k)
  have hAcoef k : 0 ≤ Acoef k := by
    simpa only [max_self] using max_le_max (hAQ k) (hAB k)
  obtain ⟨C, hC, hb⟩ := exists_selected_algebraic_forward_reserved_profiles f hΩ hRQ hKΩ hc hdom
    threshold ht output ho hoc hos π hπ hcπ hzero Acoef hAcoef
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hQr hQp hBp p o backward A α
  have hQp' k : cNorm (closedBall x RQ) k Q ≤ Acoef k * L ^ (k-Rstar) :=
    (hQp k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (zero_le_one.trans hL) _))
  have hBp' k : cNorm (closedBall x RQ) k B ≤ Acoef k * L ^ (k-Rstar) :=
    (hBp k).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg (zero_le_one.trans hL) _))
  obtain ⟨hf, hj⟩ := hb Rstar hR L ρ hL hρ Q B hQ hB hQr hQp' hBp' p o
  cases backward
  · exact ⟨hf, hj⟩
  · let a := normalizedFullAmplitude (ρ • A) ρ
    let e : V →L[ℝ] V :=
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))).prod
        ((ContinuousLinearMap.fst ℝ E (E × E)).prod
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))))
    have he : ‖e‖ ≤ 1 := by
      apply e.opNorm_le_bound zero_le_one
      intro v
      change max ‖v.2.1‖ (max ‖v.1‖ ‖v.2.2‖) ≤ 1 * ‖v‖
      rw [one_mul]
      exact max_le ((norm_fst_le v.2).trans (norm_snd_le v))
        (max_le (norm_fst_le v) ((norm_snd_le v.2).trans (norm_snd_le v)))
    let cj : CMat ≃ₗᵢ[ℝ] CMat :=
      { Matrix.conjTransposeLinearEquiv (Fin (d+1)) (Fin (d+1)) ℝ ℂ with
        norm_map' := Matrix.frobenius_norm_conjTranspose }
    have hα : α = fun v ↦ (a (e v)).conjTranspose := by
      funext v
      change ρ • (A v.2.1 v.1 (ρ • v.2.2)).conjTranspose =
        (ρ • A v.2.1 v.1 (ρ • v.2.2)).conjTranspose
      simpa only [star_trivial] using
        (Matrix.conjTranspose_smul ρ (A v.2.1 v.1 (ρ • v.2.2))).symm
    rw [hα]
    refine ⟨cj.toContinuousLinearEquiv.contDiff.comp (hf.comp e.contDiff), ?_⟩
    intro k v
    rw [norm_iteratedFDeriv_transport_conjTranspose]
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le e isOpen_univ
      hf.contDiffOn (mem_univ _) k).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) he)).trans (hj k (e v))

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
