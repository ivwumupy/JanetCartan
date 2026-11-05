module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.InactiveSourceIntegral

/-!
# The genuine inactive source gap for a literal characteristic adjoint

The adjoint differentiates the original graph phase at its source. Its gap is
`λ Dφ(z) - D_z Θ(z,ξ)`, not the forward expression `λ Dφ(z) - ξ`.
Angular separation from the actual transported graph momentum, together with
the original radial comparison, produces the quantitative gap. The existing
source integration theorem then applies to the SAME adjoint external jet.
Consumer: inactive literal-adjoint letters in
`app:ch_response:eq:fixed-factor-transfer` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
open FourierIntegral JanetCartan.Localization ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open FixedDomainInverse.FiniteResidualEnvelopes NormedSpace InnerProductSpace
variable {d r : ℕ} {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The inactive angular condition must use the original graph's transported
momentum. The same radial lower bound converts its frequency scale back to the
original `ξ`, with a fixed positive constant before `λ`
(`new:eq:carrier-ibp`). -/
theorem inactive_adjoint_source_dual_frequency_gap
    (Θ : E → E → ℝ) (φ : E → ℝ) (z ξ : E) {a δ m lam : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hm : 0 < m) (hm1 : m ≤ 1) (hlam : 0 < lam)
    (hl : a ≤ ‖gradient φ z‖)
    (hradial : m*‖ξ‖ ≤ ‖fderiv ℝ (fun y ↦ Θ y ξ) z‖)
    (hangle : gradient (fun y ↦ Θ y ξ) z ≠ 0 →
      δ ≤ dist (normalize (gradient φ z)) (normalize (gradient (fun y ↦ Θ y ξ) z))) :
    0 < (min δ 1 * min a 1 / 4)*m ∧
      ((min δ 1 * min a 1 / 4)*m) * (lam+‖ξ‖) ≤
        ‖lam • fderiv ℝ φ z - fderiv ℝ (fun y ↦ Θ y ξ) z‖ := by
  refine ⟨by positivity,?_⟩
  have hc : 0 ≤ min δ 1 * min a 1 / 4 := by positivity
  have hnorm : ‖gradient (fun y ↦ Θ y ξ) z‖ = ‖fderiv ℝ (fun y ↦ Θ y ξ) z‖ := by
    simp only [gradient,LinearIsometryEquiv.norm_map]
  have hscale : m*(lam+‖ξ‖) ≤ lam+‖gradient (fun y ↦ Θ y ξ) z‖ := by
    rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_right hm1 hlam.le]
  have h := inactive_source_dual_frequency_gap φ z (gradient (fun y ↦ Θ y ξ) z)
    ha hδ hlam hl hangle
  rw [toDual_gradient] at h
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hscale hc).trans h

/-- Arbitrary source gain for the original literal-adjoint kernel, with its
actual source gradient gap and the actual graph phase jets. No forward gap,
source-sign substitution, phase increment, or output kernel estimate is used
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem norm_inactive_adjoint_externalJet_sourceIntegral_le
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude (d+1) r)
    (φ : Par → E → ℝ) (a : Par → E → F) (q : Par × E) (ξ : E)
    (j N : ℕ) (v : Fin j → Par × E)
    {gap B M lam L K H : ℝ} (hgap : 0 < gap) (hM : 0 ≤ M)
    (hlam : 0 < lam) (hL : 0 ≤ L) (hLK : L ≤ K) (hH : 0 ≤ H)
    (hφ : ContDiffOn ℝ ∞ (φ q.1) U)
    (hΘ : ContDiffOn ℝ ∞ (fun y ↦ Θ y ξ) U)
    (hb : ∀ z ∈ U, ‖fderiv ℝ (φ q.1) z‖ ≤ B)
    (hΘb : ∀ z ∈ U, ‖fderiv ℝ (fun y ↦ Θ y ξ) z‖ ≤ M*‖ξ‖)
    (hfrequency : ∀ z ∈ U,
      gap*(lam+‖ξ‖) ≤ ‖lam • fderiv ℝ (φ q.1) z-fderiv ℝ (fun y ↦ Θ y ξ) z‖)
    (Pφ PΘ C : ℕ → ℝ)
    (hPφ : ∀ k, 0 ≤ Pφ k) (hPΘ : ∀ k, 0 ≤ PΘ k) (hC : ∀ k, 0 ≤ C k)
    (hφj : ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (φ q.1) z‖ ≤ Pφ k*L^k)
    (hΘj : ∀ z ∈ S, ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ (k+1) (fun y ↦ Θ y ξ) z‖ ≤ PΘ k*‖ξ‖*L^k)
    (hu : ContDiff ℝ ∞ (annularExternalJet true demod Θ A 0 φ lam a ξ j v q))
    (hs : tsupport (annularExternalJet true demod Θ A 0 φ lam a ξ j v q) ⊆ S)
    (huj : ∀ z ∈ S, ∀ k,
      ‖iteratedFDeriv ℝ k (annularExternalJet true demod Θ A 0 φ lam a ξ j v q) z‖ ≤
        C k*(H*K^k)) :
    ‖((2*Real.pi)^(d+1) : ℂ)⁻¹ • ∫ z,
      phaseOscillation (annularExternalPhase true demod Θ φ lam ξ q) z •
        annularExternalJet true demod Θ A 0 φ lam a ξ j v q z‖ ≤
      annularSourceKernelConstant (d+1) S gap (B+M) (fun k ↦ Pφ k+PΘ k) C N *
        (H*(K/(lam+‖ξ‖))^N) := by
  have hψ₀ : ContDiffOn ℝ ∞ (adjointCarrierSourcePhase Θ (φ q.1) lam q.2 ξ) U :=
    (contDiffOn_const.sub hΘ).add (hφ.const_smul lam)
  have hψ : ContDiffOn ℝ ∞ (annularExternalPhase true demod Θ φ lam ξ q) U := by
    have he : annularExternalPhase true demod Θ φ lam ξ q =
        adjointCarrierSourcePhase Θ (φ q.1) lam q.2 ξ -
        fun _ ↦ if demod then lam*φ q.1 q.2 else 0 := rfl
    rw [he]
    exact hψ₀.sub contDiffOn_const
  apply norm_annularSourceIntegral_le hU hS hSU _ _ ξ N hψ hu.contDiffOn hs
    hgap hH (hL.trans hLK) hlam (fun k ↦ Pφ k+PΘ k) C hC
  · intro z hz
    have hφz := (hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hΘz := (hΘ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    rw [fderiv_annularExternalPhase true demod Θ φ lam ξ q z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    simp only [ite_true]
    rw [fderiv_adjointCarrierSourcePhase Θ (φ q.1) lam q.2 ξ z hφz hΘz]
    exact hfrequency z hz
  · intro z hz
    rw [fderiv_annularExternalPhase true demod Θ φ lam ξ q z
      ((hψ₀.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    exact norm_fderiv_adjointCarrierSourcePhase_le Θ (φ q.1) hlam.le hM q.2 ξ z
      ((hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hΘ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) (hb z hz) (hΘb z hz)
  · intro z hz k hk
    rw [iteratedFDeriv_annularExternalPhase_source true demod Θ φ lam ξ q z
      (hψ₀.contDiffAt (hU.mem_nhds (hSU hz))) (k+1) (by omega)]
    exact norm_iteratedFDeriv_adjointCarrierSourcePhase_le Θ (φ q.1) hlam.le hL hLK
      q.2 ξ z (hΘ.contDiffAt (hU.mem_nhds (hSU hz)))
      (hφ.contDiffAt (hU.mem_nhds (hSU hz))) Pφ PΘ hPφ hPΘ (hφj z hz) (hΘj z hz) k hk
  · exact huj

end JanetCartan.PhysicalPrimary.CharacteristicAdjointInactive
