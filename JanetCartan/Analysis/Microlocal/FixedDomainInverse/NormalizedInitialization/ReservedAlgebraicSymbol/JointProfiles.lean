module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.FullSourceProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches

/-!
# Reserved algebraic amplitudes on the original full source parameters

Contract the actual normalized selected algebraic amplitude to the physical,
label, and full covector parameters of the primitive diagonal PDO. The fixed
projection has norm at most one. The original coefficient reserve supplies
the requested target reserve before the effective-scale compression.

Consumer: `DiagonalPdo.exists_diagonalPDO_joint_sobolev_of_primitive_jets`
in `app:ch_response:eq:direct-envelope-profile`.
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
open ResponseTransfer.DirectEvolution ResponseTransfer.DirectEvolution.CompactTransfer

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "Joint" => (E × Par) × CW
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The actual selected algebraic normalized amplitude, on the original full
source parameters, satisfies the primitive diagonal PDO reserve requirement.
This applies to the SAME solver and full residual symbols, with both literal
orientations. Constants precede both reserves, fields, and scales. Every
analytic estimate comes from the supplied retained inverse and the ORIGINAL
coefficient profiles; the output symbol profile is proved here
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem exists_selected_algebraic_joint_reserved_profiles
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
      ∀ Rorig Rcoef : ℕ, Rorig + 10 ≤ Rcoef →
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rcoef)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rcoef)) →
      ∀ (p : f.centers) (o : Fin 2) (backward : Bool),
        let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦
          π (ρ⁻¹ • ξ) • orientedMaskedPDOAmplitude false
            (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B o) y z ξ
        let α := fun (q : E × Par) (w : CW) ↦
          (ρ ^ (-1 : ℤ))⁻¹ • normalizedFullAmplitude
            (if backward then exchangedAdjointAmplitude A else A) ρ (q.1,w.fst,w.snd)
        ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ k v,
          ‖iteratedFDeriv ℝ k (Function.uncurry α) v‖ ≤ C k * L ^ (k+2-Rorig) := by
  obtain ⟨C, hC, hb⟩ := exists_selected_algebraic_full_source_reserved_profiles f hΩ hRQ hKΩ hc hdom
    threshold ht output ho hoc hos π hπ hcπ hzero AQ AB hAQ hAB
  refine ⟨C, hC, ?_⟩
  intro Rorig Rcoef hreserve L ρ hL hρ Q B hQ hB hQr hQp hBp p o backward A α
  let pr : Joint →L[ℝ] V :=
    ((ContinuousLinearMap.fst ℝ E Par).comp (ContinuousLinearMap.fst ℝ (E × Par) CW)).prod
      (((WithLp.fstL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ (E × Par) CW)).prod
        ((WithLp.sndL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ (E × Par) CW)))
  have hpr : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.1.1‖ (max ‖v.2.fst‖ ‖v.2.snd‖) ≤ 1 * ‖v‖
    rw [one_mul]
    refine max_le ((norm_fst_le v.1).trans (norm_fst_le v)) (max_le ?_ ?_)
    · exact (WithLp.norm_fst_le (p := 2) E v.2).trans (norm_snd_le v)
    · exact (WithLp.norm_snd_le (p := 2) E v.2).trans (norm_snd_le v)
  obtain ⟨ha, hj⟩ := hb Rcoef (by omega) L ρ hL hρ Q B hQ hB hQr hQp hBp p o backward
  let a := normalizedFullAmplitude (ρ • if backward then exchangedAdjointAmplitude A else A) ρ
  have he : Function.uncurry α = a ∘ pr := by
    funext v
    simp only [α, a, Function.comp_apply, _root_.zpow_neg_one, inv_inv]
    rfl
  rw [he]
  refine ⟨ha.comp pr.contDiff, ?_⟩
  intro k v
  apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr isOpen_univ
    ha.contDiffOn (mem_univ _) k).trans
  apply ((mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hpr)).trans (hj k (pr v))).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hC k)

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
