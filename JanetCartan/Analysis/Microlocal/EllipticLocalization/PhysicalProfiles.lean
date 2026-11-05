module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.Support
public import JanetCartan.Analysis.Microlocal.EllipticComplement.PositionBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.PhysicalProfiles

/-!
# All noncomparable shells of the actual elliptic factors

The original coefficient profiles produce the spatial amplitude grades without
an additional slow-scale power. The inverse and full residual retain degree
minus one on both the low and high graph shells; no high-plateau restriction
is imposed. Consumer: the noncomparable diagonal input in
`app:ch_regular:eq:high-amplitude` and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- Actual weighted spatial grades in both literal orientations. The fixed
profiles and constants precede the fields and all scales. One original
coefficient derivative is absorbed by `1 ≤ Rstar`, with offset zero and the
full `B` term retained (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_elliptic_masked_weighted_physical_profile
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (hout : ContDiff ℝ ∞ χout) (hcout : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
      ∀ backward ξ k z, z ∈ tsupport χout ×ˢ tsupport (χs) →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          orientedMaskedPDOAmplitude backward χout (χs) s w.1 w.2 ξ) z‖ ≤ C k * L ^ k := by
  obtain ⟨D, hD, hb⟩ := exists_ellipticSymbols_weighted_cNorm f hK hΩ hRQΩ
  obtain ⟨T, hT, hm⟩ := exists_orientedPDO_physical_cNorm_cost χout (χs)
    hout
    (Complex.ofRealCLM.contDiff.comp f.inputMask_smooth)
    hcout
    (f.inputMask_compact.comp_left Complex.ofReal_zero)
    x (2*f.physicalRadius) hsout
  let C k := T k * D k * (1 + AQ (k+1) + AB (k+1))
  have hC k : 0 ≤ C k := mul_nonneg (mul_nonneg (hT k) (hD k).le)
    (by linarith [hAQ (k+1), hAB (k+1)])
  refine ⟨C, hC, ?_⟩
  intro Rstar hR L hL threshold ht Q B hQ hB hmap hQl hBl hQp hBp s hs backward ξ k z hz
  obtain ⟨hsm, hj⟩ := hb threshold ht Q B hQ hB hmap hQl hBl s hs
  have hp : L ^ (k+1-Rstar) ≤ L ^ k := pow_le_pow_right₀ hL (by omega)
  have hq := (hQp (k+1)).trans (mul_le_mul_of_nonneg_left hp (hAQ _))
  have hb' := (hBp (k+1)).trans (mul_le_mul_of_nonneg_left hp (hAB _))
  have hcoeff : 1 + cNorm (closedBall x RQ) (k+1) Q + cNorm (closedBall x RQ) (k+1) B ≤
      (1 + AQ (k+1) + AB (k+1)) * L ^ k := by
    nlinarith [one_le_pow₀ hL (n := k)]
  calc
    _ ≤ (1 + ‖ξ‖) * (T k * cNorm (closedBall x (2*f.physicalRadius)) k (fun y ↦ s y ξ)) :=
      mul_le_mul_of_nonneg_left (hm s hsm backward ξ k z hz) (by positivity)
    _ = T k * ((1 + ‖ξ‖) * cNorm (closedBall x (2*f.physicalRadius)) k (fun y ↦ s y ξ)) := by ring
    _ ≤ T k * (D k * ((1 + AQ (k+1) + AB (k+1)) * L ^ k)) :=
      mul_le_mul_of_nonneg_left ((hj ξ k).trans
        (mul_le_mul_of_nonneg_left hcoeff (hD k).le)) (hT k)
    _ = C k * L ^ k := by dsimp only [C]; ring

/-- Degree minus one on every low or high noncomparable shell, for both
literal orientations of the actual elliptic inverse and residual. This
applies the physical budget producer; no symbol or leakage estimate is an
input (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elliptic_masked_noncomparable_profile
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (hout : ContDiff ℝ ∞ χout) (hcout : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 0 < ρ →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
      ∀ backward low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport χout ×ˢ tsupport (χs), ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          orientedMaskedPDOAmplitude backward χout (χs) s w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low j)) ^ (-1 : ℝ) * C k * L ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_elliptic_masked_weighted_physical_profile f hK hΩ hRQΩ
    χout hout hcout hsout
    AQ AB hAQ hAB
  refine ⟨fun k ↦ 2*C k, fun k ↦ mul_nonneg zero_le_two (hC k), ?_⟩
  intro Rstar hR L ρ hL hρ threshold ht Q B hQ hB hmap hQl hBl hQp hBp s hs
    backward low j ξ hξ z hz k
  have hh := hb Rstar hR L hL threshold ht Q B hQ hB hmap hQl hBl hQp hBp
    s hs backward (ρ • ξ) k z hz
  have hinv := (le_inv_mul_iff₀ (by positivity : 0 < 1 + ‖ρ • ξ‖)).mpr hh
  calc
    _ ≤ (1 + ‖ρ • ξ‖)⁻¹ * (C k * L ^ k) := hinv
    _ ≤ (2 * (max 1 (branchRadius low j)) ^ (-1 : ℝ)) * (C k * L ^ k) :=
      mul_le_mul_of_nonneg_right (algebraic_graph_weight_le hρ.ne' low j hξ)
        (mul_nonneg (hC k) (pow_nonneg (zero_le_one.trans hL) _))
    _ = _ := by ring

/-- Actual weighted spatial grades in both literal orientations. The fixed
profiles and constants precede the fields and all scales. One original
coefficient derivative is absorbed by `1 ≤ Rstar`, with offset zero and the
full `B` term retained (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_elliptic_oriented_weighted_physical_profile
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
      ∀ backward ξ k z, z ∈ tsupport (χo) ×ˢ tsupport (χs) →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          orientedMaskedPDOAmplitude backward (χo) (χs) s w.1 w.2 ξ) z‖ ≤ C k * L ^ k := by
  exact exists_elliptic_masked_weighted_physical_profile f hK hΩ hRQΩ (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) (elliptic_physical_carrier f).2.1
    AQ AB hAQ hAB

/-- Degree minus one on every low or high noncomparable shell, for both
literal orientations of the actual elliptic inverse and residual. This
applies the physical budget producer; no symbol or leakage estimate is an
input (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elliptic_noncomparable_profile
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 0 < ρ →
      ∀ threshold ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
      ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
        ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)),
      ∀ backward low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (χo) ×ˢ tsupport (χs), ∀ k,
        ‖iteratedFDeriv ℝ k (fun w : E × E ↦
          orientedMaskedPDOAmplitude backward (χo) (χs) s w.1 w.2 (ρ • ξ)) z‖ ≤
            (max 1 (branchRadius low j)) ^ (-1 : ℝ) * C k * L ^ k := by
  exact exists_elliptic_masked_noncomparable_profile f hK hΩ hRQΩ (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) (elliptic_physical_carrier f).2.1
    AQ AB hAQ hAB

end JanetCartan.RegularSector.EllipticLocalization
