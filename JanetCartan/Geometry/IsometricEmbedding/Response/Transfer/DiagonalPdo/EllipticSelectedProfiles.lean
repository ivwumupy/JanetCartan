module

public import JanetCartan.Analysis.Microlocal.EllipticResponseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Calculus

/-!
# Actual elliptic source profiles with the original annular selector

Apply the sharp elliptic producer on the same family and full coefficients.
The original selector controls all full-frequency jets globally, including
the low radial collar and the exchanged literal-adjoint amplitude.

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
open FourierIntegral NearCarrierAssembly NearCarrierFullLow
open RawPrimary.AmplitudeGrades.Polynomial
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The original annular selector preserves the actual elliptic symbol's
reserve at every full-source jet, including the literal exchanged adjoint.
The derivative bound is global: outside the selector's closed support all
jets vanish. The physical source/output masks, full B and radial collar
stay inside the same symbol (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_elliptic_selected_full_source_profiles
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
        let α : V → CMat := normalizedFullAmplitude
          (ρ • if backward then exchangedAdjointAmplitude A else A) ρ
        ContDiff ℝ ∞ α ∧ ∀ (k : ℕ) (v : V), ‖iteratedFDeriv ℝ k α v‖ ≤ C k * L ^ (k+2-Rstar) := by
  obtain ⟨C, hC, hb⟩ := exists_elliptic_full_source_profiles f hK hΩ hball χout ho hoc hos
    threshold ht (tsupport π) hcπ hzero AQ AB hAQ hAB
  let X := fun k ↦ cNorm (tsupport π) k π
  have hX : ∀ k, 0 ≤ X k := fun k ↦ cNorm_nonneg _ _ _
  let sm : ℝ →L[ℝ] CMat →L[ℝ] CMat := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨productProfile sm X C, productProfile_nonneg sm hX hC, ?_⟩
  intro Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual backward A α
  let a := ρ • orientedMaskedPDOAmplitude false χout (χs)
    (if residual then ellipticResidualSymbol f hK threshold Q B
      else ellipticInverseSymbol f hK threshold Q)
  let g := normalizedFullAmplitude (if backward then exchangedAdjointAmplitude a else a) ρ
  obtain ⟨ha, hja, har, hjar⟩ := hb Rstar hR L ρ hL hρ Q B hQ hB hmap hQp hBp residual false
  have hg : ContDiff ℝ ∞ g := by cases backward <;> assumption
  have hgj : ∀ k v, v.2.2 ∈ tsupport π →
      ‖iteratedFDeriv ℝ k g v‖ ≤ C k * L ^ (k-(Rstar-2)) := by
    cases backward <;> assumption
  let pr : V →L[ℝ] E := (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  have hpr : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro v
    change ‖v.2.2‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact (norm_snd_le v.2).trans (norm_snd_le v)
  have hpj (k) (v : V) : ‖iteratedFDeriv ℝ k (π ∘ pr) v‖ ≤ X k := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr isOpen_univ
      hπ.contDiffOn (mem_univ _) k).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr)).trans
    by_cases hv : pr v ∈ tsupport π
    · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hcπ
        (fun z _ ↦ hπ.contDiffAt.of_le (by simp)) hv le_rfl
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hv ((tsupport_iteratedFDeriv_subset k) hh)), norm_zero]
      exact hX k
  have hρne : ρ ≠ 0 := (zero_lt_one.trans_le hρ).ne'
  have he : α = fun v ↦ π (pr v) • g v := by
    cases backward <;> funext v <;>
      simp only [α, A, g, a, pr, normalizedFullAmplitude, exchangedAdjointAmplitude,
        orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, Pi.smul_apply,
        ContinuousLinearMap.comp_apply,
        inv_smul_smul₀ hρne, Matrix.conjTranspose_smul, star_trivial]
    all_goals exact smul_comm _ _ _
  rw [he]
  refine ⟨(hπ.comp pr.contDiff).smul hg, ?_⟩
  intro k v
  by_cases hv : pr v ∈ tsupport π
  · have hh := jet_bilinear_le sm isOpen_univ (hπ.comp pr.contDiff).contDiffOn
      hg.contDiffOn (mem_univ v) (b := Rstar-2) hL hX hC
      (fun j ↦ (hpj j v).trans (le_mul_of_one_le_right (hX j) (one_le_pow₀ hL)))
      (fun j ↦ hgj j v hv) k
    simpa only [show k-(Rstar-2) = k+2-Rstar by omega, sm, Function.comp_apply, ContinuousLinearMap.lsmul_apply] using hh
  · have hs : tsupport (fun v : V ↦ π (pr v) • g v) ⊆ pr ⁻¹' tsupport π :=
      (tsupport_smul_subset_left _ _).trans (tsupport_comp_subset_preimage π pr.continuous)
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hv (hs ((tsupport_iteratedFDeriv_subset k) hh))), norm_zero]
    exact mul_nonneg (productProfile_nonneg sm hX hC k) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ResponseTransfer.DiagonalPdo
