module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Integration
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.JetIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.OriginalPhase

/-!
# Nonstationary integration of the actual normalized external jets

The intermediate amplitude input is produced by
`exists_originalAnnularExternalJet_profile` and discharged in the consuming
original-primitive kernel theorem. The source phase is the literal elapsed
phase; the source gap is deduced from the fixed annulus and original radial
comparison. Source: `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization AmplitudeJets
variable {d r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)

set_option backward.isDefEq.respectTransparency false in
/-- Integration of either physical or demodulated external jet, retaining
one source gain per integration. The amplitude premise is internal and has
an original-primitive producer. Consumer: `exists_originalAnnularSourceKernel_profile`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_annularExternalJet_sourceIntegral_le
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude (d + 1) r)
    (π : E → ℂ) (φ : P → E → ℝ) (a : P → E → F) (p : P × E) (ξ : E)
    (j N : ℕ) (v : Fin j → P × E)
    {a₀ B m M lam L K H : ℝ} (ha₀ : 0 < a₀) (hB : 0 < B)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    (hlam : 0 < lam) (hL : 0 ≤ L) (hLK : L ≤ K) (hH : 0 ≤ H)
    (hφ : ContDiffOn ℝ ∞ (φ p.1) U)
    (hΘ : ContDiffOn ℝ ∞ (fun z => Θ z ξ) U)
    (hl : ∀ z ∈ U, a₀ ≤ ‖fderiv ℝ (φ p.1) z‖)
    (hb : ∀ z ∈ U, ‖fderiv ℝ (φ p.1) z‖ ≤ B)
    (hvl : ∀ z ∈ U, m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => Θ y ξ) z‖)
    (hvu : ∀ z ∈ U, ‖fderiv ℝ (fun y => Θ y ξ) z‖ ≤ M * ‖ξ‖)
    (hfar : 1 - annularSelector (a₀ / (2 * M)) (2 * B / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0)
    (Pφ PΘ C : ℕ → ℝ) (hPφ : ∀ k, 0 ≤ Pφ k) (hPΘ : ∀ k, 0 ≤ PΘ k)
    (hC : ∀ k, 0 ≤ C k)
    (hφj : ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (φ p.1) z‖ ≤ Pφ k * L ^ k)
    (hΘj : ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k + 1) (fun y => Θ y ξ) z‖ ≤ PΘ k * (lam + ‖ξ‖) * L ^ k)
    (hu : ContDiff ℝ ∞ (annularExternalJet adj demod Θ A π φ lam a ξ j v p))
    (hs : tsupport (annularExternalJet adj demod Θ A π φ lam a ξ j v p) ⊆ S)
    (huj : ∀ z ∈ S, ∀ k,
      ‖iteratedFDeriv ℝ k (annularExternalJet adj demod Θ A π φ lam a ξ j v p) z‖ ≤
        C k * (H * K ^ k)) :
    ‖((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ • ∫ z,
      phaseOscillation (annularExternalPhase adj demod Θ φ lam ξ p) z •
        annularExternalJet adj demod Θ A π φ lam a ξ j v p z‖ ≤
      annularSourceKernelConstant (d + 1) S (radialGapConstant a₀ B * m) (B + M)
        (fun k => Pφ k + PΘ k) C N * (H * (K / (lam + ‖ξ‖)) ^ N) := by
  have hψ₀ : ContDiffOn ℝ ∞
      (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
        else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) U := by
    cases adj
    · exact (contDiffOn_const.sub ((contDiff_id.inner ℝ contDiff_const).contDiffOn)).add
        (hφ.const_smul lam)
    · exact (contDiffOn_const.sub hΘ).add (hφ.const_smul lam)
  have hψ : ContDiffOn ℝ ∞ (annularExternalPhase adj demod Θ φ lam ξ p) U := by
    have he : annularExternalPhase adj demod Θ φ lam ξ p =
        (if adj then adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ
          else forwardCarrierSourcePhase Θ (φ p.1) lam p.2 ξ) -
        fun _ => if demod then lam * φ p.1 p.2 else 0 := by
      funext w
      cases adj <;> rfl
    rw [he]
    exact hψ₀.sub contDiffOn_const
  apply norm_annularSourceIntegral_le hU hS hSU _ _ ξ N hψ hu.contDiffOn hs
    (mul_pos (radialGapConstant_pos ha₀ hB) hm) hH (hL.trans hLK) hlam
    (fun k => Pφ k + PΘ k) C hC
  · intro z hz
    rw [fderiv_annularExternalPhase adj demod Θ φ lam ξ p z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    have hφz := (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hΘz := (hΘ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    cases adj
    · exact forwardCarrierSourcePhase_gap Θ (φ p.1) ha₀ hB hm hm1 hM1 hlam
        p.2 ξ z hφz (hl z hz) (hb z hz) hfar
    · exact adjointCarrierSourcePhase_gap Θ (φ p.1) ha₀ hB hm hm1 (by positivity) hlam
        p.2 ξ z hφz hΘz (hl z hz) (hb z hz) (hvl z hz) (hvu z hz) hfar
  · intro z hz
    rw [fderiv_annularExternalPhase adj demod Θ φ lam ξ p z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    have hφz := (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hΘz := (hΘ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    cases adj
    · exact (norm_fderiv_forwardCarrierSourcePhase_le Θ (φ p.1) hlam.le p.2 ξ z
        hφz (hb z hz)).trans (by gcongr)
    · exact norm_fderiv_adjointCarrierSourcePhase_le Θ (φ p.1) hlam.le (by positivity)
        p.2 ξ z hφz hΘz (hb z hz) (hvu z hz)
  · intro z hz k hk
    rw [iteratedFDeriv_annularExternalPhase_source adj demod Θ φ lam ξ p z
      (hψ₀.contDiffAt (hU.mem_nhds (hSU hz))) (k + 1) (by omega)]
    have hφz := hφ.contDiffAt (hU.mem_nhds (hSU hz))
    have hΘz := hΘ.contDiffAt (hU.mem_nhds (hSU hz))
    cases adj
    · exact (norm_iteratedFDeriv_forwardCarrierSourcePhase_le Θ (φ p.1) hlam.le hL hLK
        p.2 ξ z hφz Pφ hPφ (hφj z hz) k hk).trans (by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hPΘ k))
              (add_nonneg hlam.le (norm_nonneg ξ))) (pow_nonneg (hL.trans hLK) k))
    · simp only [ite_true]
      rw [iteratedFDeriv_adjointCarrierSourcePhase Θ (φ p.1) lam p.2 ξ z
        hΘz hφz (k + 1) (by omega)]
      calc
        _ ≤ ‖lam • iteratedFDeriv ℝ (k + 1) (φ p.1) z‖ +
            ‖iteratedFDeriv ℝ (k + 1) (fun y => Θ y ξ) z‖ := norm_sub_le _ _
        _ = lam * ‖iteratedFDeriv ℝ (k + 1) (φ p.1) z‖ +
            ‖iteratedFDeriv ℝ (k + 1) (fun y => Θ y ξ) z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        _ ≤ lam * (Pφ k * L ^ k) + PΘ k * (lam + ‖ξ‖) * L ^ k := by
              gcongr
              · exact hφj z hz k hk
              · exact hΘj z hz k hk
        _ ≤ (lam + ‖ξ‖) * (Pφ k * L ^ k) + PΘ k * (lam + ‖ξ‖) * L ^ k := by
              exact add_le_add (mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right (norm_nonneg ξ))
                (mul_nonneg (hPφ k) (pow_nonneg hL k))) le_rfl
        _ = (Pφ k + PΘ k) * (lam + ‖ξ‖) * L ^ k := by ring
        _ ≤ _ := by
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLK k)
                (mul_nonneg (add_nonneg (hPφ k) (hPΘ k))
                  (add_nonneg hlam.le (norm_nonneg ξ)))
  · exact huj

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
