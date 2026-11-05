module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.JetIntegration
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.AngularGap

/-!
# Inactive source integration for the actual forward retarded factor

The final incidence cutoff gives an angular gap on every physical frequency
in the original source mask. Its lower gradient band gives the exact dual
frequency gap. The existing nonstationary integral theorem then applies to
the original normalized external jet, including the source cutoff and its
position-dependent amplitude. No Fourier-factorization identity is presumed.

Consumer: the inactive half of the characteristic finite-word estimate
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open FourierIntegral JanetCartan.Localization ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open NormedSpace InnerProductSpace
variable {d r : ℕ} {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The actual angular separation is the exact dual-space source gap used
inside the full retarded integral. This applies to either sign of the original
source phase, by using its actual gradient (`new:eq:carrier-ibp`). -/
theorem inactive_source_dual_frequency_gap
    (φ : E → ℝ) (x ξ : E) {a δ lam : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hlam : 0 < lam)
    (hl : a ≤ ‖gradient φ x‖)
    (hangle : ξ ≠ 0 → δ ≤ dist (normalize (gradient φ x)) (normalize ξ)) :
    (min δ 1 * min a 1 / 4) * (lam+‖ξ‖) ≤
      ‖lam • fderiv ℝ φ x - toDual ℝ E ξ‖ := by
  have he : lam • fderiv ℝ φ x - toDual ℝ E ξ =
      toDual ℝ E (lam • gradient φ x - ξ) := by
    rw [map_sub,map_smul,toDual_gradient]
  rw [he,LinearIsometryEquiv.norm_map]
  exact SignedProductEstimates.full_frequency_gap_of_normalized_distance
    ha hδ hlam hl hangle

/-- The same full kernel, without an annular truncation, has arbitrary
source gain whenever the actual forward carrier is inactive. The amplitude
jet input is supplied by `exists_originalAnnularExternalJet_profile` with
selector zero. The coefficient constants remain fixed before integration
order (`app:ch_response:lem:energy-carrier-jets`). -/
theorem norm_inactive_forward_externalJet_sourceIntegral_le
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude (d+1) r)
    (φ : Par → E → ℝ) (a : Par → E → F) (q : Par × E) (ξ : E)
    (j N : ℕ) (v : Fin j → Par × E)
    {gap B lam L K H : ℝ} (hgap : 0 < gap)
    (hlam : 0 < lam) (hL : 0 ≤ L) (hLK : L ≤ K) (hH : 0 ≤ H)
    (hφ : ContDiffOn ℝ ∞ (φ q.1) U)
    (hb : ∀ z ∈ U, ‖fderiv ℝ (φ q.1) z‖ ≤ B)
    (hfrequency : ∀ z ∈ U,
      gap*(lam+‖ξ‖) ≤ ‖lam • fderiv ℝ (φ q.1) z-toDual ℝ E ξ‖)
    (Pφ C : ℕ → ℝ) (hPφ : ∀ k, 0 ≤ Pφ k) (hC : ∀ k, 0 ≤ C k)
    (hφj : ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (φ q.1) z‖ ≤ Pφ k*L^k)
    (hu : ContDiff ℝ ∞ (annularExternalJet false demod Θ A 0 φ lam a ξ j v q))
    (hs : tsupport (annularExternalJet false demod Θ A 0 φ lam a ξ j v q) ⊆ S)
    (huj : ∀ z ∈ S, ∀ k,
      ‖iteratedFDeriv ℝ k (annularExternalJet false demod Θ A 0 φ lam a ξ j v q) z‖ ≤
        C k*(H*K^k)) :
    ‖((2*Real.pi)^(d+1) : ℂ)⁻¹ • ∫ z,
      phaseOscillation (annularExternalPhase false demod Θ φ lam ξ q) z •
        annularExternalJet false demod Θ A 0 φ lam a ξ j v q z‖ ≤
      annularSourceKernelConstant (d+1) S gap (B+1) Pφ C N *
        (H*(K/(lam+‖ξ‖))^N) := by
  have hψ₀ : ContDiffOn ℝ ∞ (forwardCarrierSourcePhase Θ (φ q.1) lam q.2 ξ) U :=
    (contDiffOn_const.sub ((contDiff_id.inner ℝ contDiff_const).contDiffOn)).add
      (hφ.const_smul lam)
  have hψ : ContDiffOn ℝ ∞ (annularExternalPhase false demod Θ φ lam ξ q) U := by
    have he : annularExternalPhase false demod Θ φ lam ξ q =
        forwardCarrierSourcePhase Θ (φ q.1) lam q.2 ξ -
        fun _ ↦ if demod then lam*φ q.1 q.2 else 0 := rfl
    rw [he]
    exact hψ₀.sub contDiffOn_const
  apply norm_annularSourceIntegral_le hU hS hSU _ _ ξ N hψ hu.contDiffOn hs
    hgap hH (hL.trans hLK) hlam Pφ C hC
  · intro z hz
    have hφz := (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    rw [fderiv_annularExternalPhase false demod Θ φ lam ξ q z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    simp only [Bool.false_eq_true,ite_false]
    rw [fderiv_forwardCarrierSourcePhase Θ (φ q.1) lam q.2 ξ z hφz]
    exact hfrequency z hz
  · intro z hz
    rw [fderiv_annularExternalPhase false demod Θ φ lam ξ q z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    exact norm_fderiv_forwardCarrierSourcePhase_le Θ (φ q.1) hlam.le q.2 ξ z
      ((hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) (hb z hz)
  · intro z hz k hk
    rw [iteratedFDeriv_annularExternalPhase_source false demod Θ φ lam ξ q z
      (hψ₀.contDiffAt (hU.mem_nhds (hSU hz))) (k+1) (by omega)]
    exact norm_iteratedFDeriv_forwardCarrierSourcePhase_le Θ (φ q.1) hlam.le hL hLK
      q.2 ξ z (hφ.contDiffAt (hU.mem_nhds (hSU hz))) Pφ hPφ (hφj z hz) k hk
  · exact huj

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
