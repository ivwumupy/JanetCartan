module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.EllipticSelectedProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Calculus

/-!
# Actual elliptic jets on the original full source parameters

The actual selected symbol is composed with the contractive physical and
frequency projection. The original label and covector remain independent;
both orientations keep their original profile constants and reserve.

Sources: `app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open RegularSector.EllipticResponseProfiles ArbitraryAccuracy.ResidualLocalization
open FourierIntegral NearCarrierAssembly NearCarrierFullLow DirectEvolution DirectEvolution.CompactTransfer
open RawPrimary.AmplitudeGrades.Polynomial
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
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Apply the actual selected elliptic profiles to the original independent
full source parameters. The physical/frequency projection is contractive,
so the original constant and reserve are unchanged in both literal
orientations (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_elliptic_selected_joint_profiles
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 2 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ (residual backward : Bool),
        let A : FullAmplitude (d+1) (d+1) := fun a b ξ ↦ π (ρ⁻¹ • ξ) • orientedMaskedPDOAmplitude false χout (χs)
          (if residual then ellipticResidualSymbol f hK threshold Q B
            else ellipticInverseSymbol f hK threshold Q) a b ξ
        let α := fun (q : E × Par) (w : CW) ↦
          (ρ ^ (-1 : ℤ))⁻¹ • normalizedFullAmplitude
            (if backward then exchangedAdjointAmplitude A else A) ρ (q.1,w.fst,w.snd)
        ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ k v,
          ‖iteratedFDeriv ℝ k (Function.uncurry α) v‖ ≤ C k * L ^ (k+2-Rstar) := by
  obtain ⟨C, hC, hb⟩ := exists_elliptic_selected_full_source_profiles f hK hΩ hball
    χout ho hoc hos threshold ht π hπ hcπ hzero AQ AB hAQ hAB
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward A α
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
  obtain ⟨ha, hj⟩ := hb Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward
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
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr)).trans (hj k (pr v))

end JanetCartan.ResponseTransfer.DiagonalPdo