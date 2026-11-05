module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.Annular
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches

/-!
# The actual reserved endpoint on the original full source parameters

The physical/frequency projection from the original independent product
parameters is contractive. Thus the SAME endpoint amplitude, original
annular selector and both literal orientations satisfy the exact primitive
jet input of `DiagonalPdo.exists_diagonalPDO_joint_sobolev_of_primitive_jets`.
No source parameter is identified with a physical coordinate.

Sources: `app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:eq:fixed-factor-transfer`, and
`app:ch_regular_base:eq:energy-complete-residual`.
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
open ResidualLocalization ResponseTransfer ResponseTransfer.NearCarrierFullLow FourierIntegral
open ResponseTransfer.DirectEvolution

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "Joint" => (E × Par) × CW

/-- The literal normalized endpoint annulus has global joint smoothness
and the exact reserved primitive profile required by the forward and adjoint
full-source PDO theorems. The entire analytic estimate is produced from the
original coefficient profiles and the SAME retained `W₁` certificate, with
all constants chosen before the reserve, frequency, history and amplitude
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_selected_endpoint_reserved_joint_profiles
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
      let α := fun (q : E × Par) (w : CW) ↦
        (ρ ^ (-1 : ℤ))⁻¹ • normalizedFullAmplitude
          (if backward then exchangedAdjointAmplitude A else A) ρ (q.1,w.fst,w.snd)
      ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ k v,
        ‖iteratedFDeriv ℝ k (Function.uncurry α) v‖ ≤ D k * L ^ (k+2-Rreserve) := by
  obtain ⟨C, hC, hb⟩ := exists_selected_endpoint_reserved_annular_profiles
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
    π hπ hcπ hzero AQ AB cost hAQ hAB hcost
  refine ⟨C, hC, ?_⟩
  intro Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W J hW hbudget p backward A α
  let pr : Joint →L[ℝ] V :=
    ((ContinuousLinearMap.fst ℝ E Par).comp (ContinuousLinearMap.fst ℝ (E × Par) CW)).prod
      (((WithLp.fstL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ (E × Par) CW)).prod
        ((WithLp.sndL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ (E × Par) CW)))
  have hpr : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.1.1‖ (max ‖v.2.fst‖ ‖v.2.snd‖) ≤ 1*‖v‖
    rw [one_mul]
    refine max_le ((norm_fst_le v.1).trans (norm_fst_le v)) (max_le ?_ ?_)
    · exact (WithLp.norm_fst_le (p := 2) E v.2).trans (norm_snd_le v)
    · exact (WithLp.norm_snd_le (p := 2) E v.2).trans (norm_snd_le v)
  obtain ⟨ha, hj⟩ := hb Rreserve Rcoeff hR L ρ hL hρ Q hQ B hQp hBp W hW hbudget p backward
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
  apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr)).trans
  exact (hj k (pr v)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega : k-Rreserve ≤ k+2-Rreserve)) (hC k))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
