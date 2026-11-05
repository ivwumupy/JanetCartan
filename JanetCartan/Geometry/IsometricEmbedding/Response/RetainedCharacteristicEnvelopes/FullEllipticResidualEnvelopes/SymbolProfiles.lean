module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.PositionBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Global physical jets of the complete masked elliptic symbol

The complementary source integral in `app:ch_response:eq:direct-envelope-profile`
keeps each physical frequency fixed.  The original elliptic position estimates
therefore supply its complete amplitude profile, including the temporal
covector and all frequencies outside the chosen normalized annulus.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open RegularSector RegularSector.FiniteMasks.ActualFamily EllipticComplement
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

private theorem masked_position_jet_le {S : Set E} (hS : IsCompact S)
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχS : tsupport χ ⊆ S)
    (a : E → CMat) (ha : ContDiff ℝ ∞ a) (k : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ k (fun z ↦ χ z • a z) y‖ ≤
      ((k+1 : ℝ) * 2^k * cNorm S k χ) * cNorm S k a := by
  by_cases hy : y ∈ S
  · exact (norm_iteratedFDeriv_le_cNorm hS
      ((hχ.smul ha).of_le (by simp)) hy le_rfl).trans
      (cNorm_smul_on_open_le hS isOpen_univ (subset_univ _)
        hχ.contDiffOn ha.contDiffOn k)
  · have hz : iteratedFDeriv ℝ k (fun z ↦ χ z • a z) y = 0 := by
      by_contra hn
      exact hy (hχS (tsupport_smul_subset_left χ a (support_iteratedFDeriv_subset k hn)))
    rw [hz, norm_zero]
    have := cNorm_nonneg S k χ
    have := cNorm_nonneg S k a
    positivity

/-- The actual full inverse and differentiated residual, with the supplied
output mask, satisfy global physical jet bounds at every fixed full frequency.
Constants precede the histories, coefficient scale, covector and symbol choice.
The one-derivative elliptic reserve is retained, so `Rstar ≥ 1` suffices for the
coarse source-kernel profile.  No annular truncation or symbol estimate is
assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_complete_elliptic_masked_position_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout)
    (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ Rstar : ℕ, 1 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) 1 Q ≤ M → cNorm (closedBall x RQ) 0 B ≤ M →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L^(k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L^(k-Rstar)) →
      ∀ residual : Bool,
        let a := fun y ξ ↦ χout y •
          (if residual then ellipticResidualSymbol f hK threshold Q B y ξ
            else ellipticInverseSymbol f hK threshold Q y ξ)
        ContDiff ℝ ∞ (Function.uncurry a) ∧
        ∀ (k : ℕ) (ξ y : E), ‖iteratedFDeriv ℝ k (fun z ↦ a z ξ) y‖ ≤ C k * L^k := by
  obtain ⟨D, hD, hbounds⟩ := exists_ellipticSymbols_weighted_cNorm f hK hΩ hRQΩ
  let S := closedBall x (2*f.physicalRadius)
  let C := fun k : ℕ ↦ (((k+1 : ℝ) * 2^k * cNorm S k χout) * D k) *
    (1 + AQ (k+1) + AB (k+1))
  have hC (k : ℕ) : 0 ≤ C k := by
    dsimp only [C]
    have := cNorm_nonneg S k χout
    exact mul_nonneg (mul_nonneg (by positivity) (hD k).le)
      (by linarith [hAQ (k+1), hAB (k+1)])
  refine ⟨C,hC,?_⟩
  intro threshold hthreshold Rstar hRstar L hL Q B hQ hB hmap hQl hBl hQp hBp residual a
  let σ := fun y ξ ↦ if residual then ellipticResidualSymbol f hK threshold Q B y ξ
    else ellipticInverseSymbol f hK threshold Q y ξ
  have hσmem : σ ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B} : Set (E → E → CMat)) := by
    cases residual <;> simp [σ]
  obtain ⟨hσ,hσbounds⟩ := hbounds threshold hthreshold Q B hQ hB hmap hQl hBl σ hσmem
  have ha : ContDiff ℝ ∞ (Function.uncurry a) :=
    (ho.comp contDiff_fst).smul hσ
  refine ⟨ha,?_⟩
  intro k ξ y
  have hj : cNorm S k (fun z ↦ σ z ξ) ≤
      D k * (1 + cNorm (closedBall x RQ) (k+1) Q + cNorm (closedBall x RQ) (k+1) B) := by
    apply (le_mul_of_one_le_left (cNorm_nonneg _ _ _)
      (by linarith [norm_nonneg ξ] : 1 ≤ 1+‖ξ‖)).trans
    exact hσbounds ξ k
  have hscale : 1 + cNorm (closedBall x RQ) (k+1) Q + cNorm (closedBall x RQ) (k+1) B ≤
      (1 + AQ (k+1) + AB (k+1)) * L^k := by
    have hs : L^(k+1-Rstar) ≤ L^k := pow_le_pow_right₀ hL (by omega)
    have hq := (hQp (k+1)).trans (mul_le_mul_of_nonneg_left hs (hAQ _))
    have hb := (hBp (k+1)).trans (mul_le_mul_of_nonneg_left hs (hAB _))
    have hp : (1 : ℝ) ≤ L^k := one_le_pow₀ hL
    nlinarith
  have hb := masked_position_jet_le (isCompact_closedBall _ _) χout ho hos
    (fun z ↦ σ z ξ) (hσ.comp (contDiff_id.prodMk contDiff_const)) k y
  change ‖iteratedFDeriv ℝ k (fun z ↦ χout z • σ z ξ) y‖ ≤ _
  apply hb.trans
  calc
    _ ≤ ((k+1 : ℝ) * 2^k * cNorm S k χout) *
        (D k * ((1 + AQ (k+1) + AB (k+1)) * L^k)) :=
      mul_le_mul_of_nonneg_left (hj.trans
        (mul_le_mul_of_nonneg_left hscale (hD k).le))
          (mul_nonneg (by positivity) (cNorm_nonneg S k χout))
    _ = C k * L^k := by dsimp only [C]; ring

/-- Absorbing the supplied output into the symbol preserves the original
complete amplitude.  The outer mask is the original input mask, already
proved to equal one on the output support
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem inputMask_mul_masked_elliptic_amplitude
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (χout : E → ℂ) (hos : tsupport χout ⊆ closedBall x (2*f.physicalRadius))
    (a : E → E → CMat) (y z ξ : E) :
    ((f.inputMask y : ℂ) * (f.inputMask z : ℂ)) • (χout y • a y ξ) =
      (χout y * (f.inputMask z : ℂ)) • a y ξ := by
  by_cases hy : χout y = 0
  · simp only [hy, zero_smul, smul_zero, zero_mul]
  · have hm : f.inputMask y = 1 := interior_subset (s := {u | f.inputMask u = 1})
      (f.inputMask_plateau (hos (subset_tsupport χout hy)))
    simp only [hm, Complex.ofReal_one, one_mul, smul_smul]
    rw [mul_comm]

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
