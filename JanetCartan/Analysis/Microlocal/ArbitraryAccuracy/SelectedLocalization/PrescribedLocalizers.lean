module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.OrdinaryLocalizer
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SelectedLocalizerLow

/-!
# Realizations of the prescribed nested masks

The terminal-protection producer supplies the mask witnesses together with their
terminal plateau. Apply the primitive localizer calculus to those exact symbols;
no existential mask family is chosen here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential FiniteChain.Graph
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The primitive joint profile controls the two quantizations of the supplied
mask, with one constant before the mask or frequency. This applies to the exact
witnesses of `NormalizedTerminalProtection.SelectedApplication`, without
selecting another existential mask (`app:ch_regular:lem:finite-chain`). -/
theorem exists_prescribed_localizer_low_constant
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : LocalizerSymbol (d+1)), ContDiff ℝ ∞ m → HasCompactSupport m →
      tsupport m ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      (∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ Hmask k) →
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ R Lout : H →L[ℂ] H,
      (∀ u, R u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ m (fun z ↦ (u z).ofLp) y)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ m (fun z ↦ (u z).ofLp) y)) →
      ‖R‖ ≤ C ∧ ‖Lout‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_leftLocalizer_primitive_sobolev_bound
    (r := d+1) (closedBall (0 : E) Rbase) (isCompact_closedBall _ _)
    Hmask hHmask 0 (le_max_left 0 b) 0
  refine ⟨C, hC, ?_⟩
  intro m hm hmc hsupp hjets ρ hρ R Lout hR hLout
  have hbase : Prod.fst '' tsupport m ⊆ closedBall (0 : E) Rbase := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hsupp hp).1
  have hann : ∀ p ∈ tsupport m, ‖p.2‖ ≤ max 0 b := by
    intro p hp
    have h := (hsupp hp).2
    simp only [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_right _ _)
  have hgrades (l : ℕ) (p : E × E) :
      ‖iteratedFDeriv ℝ l m p‖ ≤ Hmask l * (1 : ℝ) ^ (l+0) := by
    simpa only [one_pow, mul_one] using hjets l p
  have hleft (M : H →L[ℂ] H)
      (hM : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ m (fun z ↦ (u z).ofLp) y)) : ‖M‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    have h := hbound m hm hmc hbase hann ρ 1 hρ le_rfl hgrades M hM u
    simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, pow_zero, one_pow,
      mul_one] using h.2
  refine ⟨?_, hleft Lout hLout⟩
  have h := hleft R.adjoint
    (ResidualLocalization.IdentityDefect.leftLocalizer_adjoint_ae_of_rightLocalizer
      (ne_of_gt (zero_lt_one.trans_le hρ)) m hm.continuous hmc R hR)
  simpa only [ContinuousLinearMap.adjoint.norm_map] using h

/-- Realize every supplied nested mask with its literal left/right pair and
one low constant preceding all masks. The terminal-protection witness is kept
verbatim (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_bounded_localizers_with_uniform_low
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∀ (m : Fin (N+1) → LocalizerSymbol (d+1)),
      (∀ k, ContDiff ℝ ∞ (m k)) → (∀ k, HasCompactSupport (m k)) →
      (∀ k, tsupport (m k) ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b) →
      (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ Hmask l) →
      ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ R Lout : Fin (N+1) → H →L[ℂ] H, ∀ k,
        R k = (Lout k).adjoint ∧
        (∀ u, R k u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout k u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        ‖R k‖ ≤ C ∧ ‖Lout k‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_prescribed_localizer_low_constant b Rbase Hmask hHmask
  refine ⟨C, hC, ?_⟩
  intro N m hm hmc hsupp hjets ρ hρ
  choose Lout hleft hright using fun k : Fin (N+1) ↦
    EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers (q := d+1)
      (ne_of_gt (zero_lt_one.trans_le hρ)) (m k) (hm k).continuous (hmc k)
  refine ⟨fun k ↦ (Lout k).adjoint, Lout, fun k ↦ ⟨rfl, hright k, hleft k, ?_⟩⟩
  exact hbound (m k) (hm k) (hmc k) (hsupp k) (hjets k) ρ hρ
    (Lout k).adjoint (Lout k) (hright k) (hleft k)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
