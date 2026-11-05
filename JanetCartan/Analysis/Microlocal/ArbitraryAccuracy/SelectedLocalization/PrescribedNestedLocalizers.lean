module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedLocalizers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedCrossQuantization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedTerminalRight

/-!
# Analytic localizers on the exact terminal-protected nested family

One realization of every prescribed symbol supplies low bounds, the change
between quantizations and the terminal right defect. All constants precede
the varying family. The masks and terminal operator are never reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral
open LocalSobolev RegularSector.Characteristic.RetardedLocalization
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Realize the exact mask witnesses supplied with the prescribed terminal
plateau, then apply every localizer estimate needed by the alternating chain.
The primitive geometric hypotheses are conclusions of
`NormalizedTerminalProtection.exists_selected_terminal_even_proof_masks_of_coefficient_bound`.
No new mask is selected and no analytic leakage estimate is an input
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_nested_localizer_estimates
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∃ Ccross Cterminal : ℕ → ℕ → ℝ,
      (∀ s q, 0 ≤ Ccross s q) ∧ (∀ s q, 0 ≤ Cterminal s q) ∧
      ∀ (N : ℕ) (m : Fin (N+1) → LocalizerSymbol (d+1)),
      (∀ k, ContDiff ℝ ∞ (m k)) → (∀ k, HasCompactSupport (m k)) →
      (∀ k p, m k p ∈ Icc (0 : ℝ) 1) →
      (∀ k, tsupport (m k) ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b) →
      (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ Hmask l) →
      (∀ k : Fin N, ∀ p ∈ tsupport (m k.castSucc),
        closedBall p buffer ⊆ interior {z | m k.succ z = 1}) →
      (∀ k, ∀ p ∈ tsupport (m k), closedBall p buffer ⊆ interior {z | mt z = 1}) →
      ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ R Lout : Fin (N+1) → H →L[ℂ] H,
      (∀ k, R k = (Lout k).adjoint ∧
        (∀ u, R k u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout k u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        ‖R k‖ ≤ C0 ∧ ‖Lout k‖ ≤ C0) ∧
      ∀ L : ℝ, 1 ≤ L → L ≤ ρ → ∀ Mt : H →L[ℂ] H,
      (∀ u, Mt u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mt (fun z ↦ (u z).ofLp) y)) →
      ∀ (k : Fin N) (s q : ℕ) (backward : Bool)
        (u : LocalL2 (univ : Set E) (EuclideanSpace ℂ (Fin (d+1)))),
      let G := restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ
      let S := (1-localRetardedOperator MeasurableSet.univ univ (R k.succ)).comp
        (localRetardedOperator MeasurableSet.univ univ (Lout k.castSucc))
      let v := (if backward then S.adjoint else S) u
      let w := (1-localRetardedOperator MeasurableSet.univ univ Mt)
        (localRetardedOperator MeasurableSet.univ univ (R k.castSucc) u)
      (v ∈ G.level s ∧ G.gradeNorm s v ≤
        Ccross s q*ρ^s*L^(s+(d+1+1))*(L/ρ)^q*‖u‖) ∧
      (w ∈ G.level s ∧ G.gradeNorm s w ≤
        Cterminal s q*ρ^(2*(d+1)+s)*L^(s+(d+1+1))*(L/ρ)^q*‖u‖) := by
  obtain ⟨C0,hC0,hlocalizers⟩ := exists_prescribed_bounded_localizers_with_uniform_low
    b Rbase Hmask hHmask
  obtain ⟨Ccross,hCcross,hcross⟩ := exists_prescribed_cross_quantization_restriction_constants
    b Rbase Hmask hHmask hbuffer
  choose Cterminal hCterminal hterminal using fun s ↦
    exists_prescribed_terminal_right_restriction_constants b Rbase Hmask hHmask mt ht htc hbuffer s
  refine ⟨C0,hC0,Ccross,Cterminal,hCcross,hCterminal,?_⟩
  intro N m hm hmc hmr hsupp hjets hlink htlink ρ hρ
  obtain ⟨R,Lout,hrealize⟩ := hlocalizers N m hm hmc hsupp hjets ρ hρ
  refine ⟨R,Lout,hrealize,?_⟩
  intro L hL hLρ Mt hMt k s q backward u G S v w
  constructor
  · exact hcross (m k.castSucc) (m k.succ)
      (hm k.castSucc) (hmc k.castSucc) (hm k.succ) (hmc k.succ)
      (hsupp k.castSucc) (hjets k.castSucc) (hjets k.succ) (hlink k)
      ρ L hL hLρ (Lout k.castSucc) (R k.succ)
      (hrealize k.castSucc).2.2.1 (hrealize k.succ).2.1 s q backward u
  · exact hterminal s (m k.castSucc) (m k.succ)
      (hm k.castSucc) (hmc k.castSucc) (hm k.succ) (hmc k.succ) (hmr k.succ)
      (hsupp k.castSucc) (hsupp k.succ) (hjets k.castSucc) (hjets k.succ)
      (hlink k) (htlink k.succ) ρ L hL hLρ (R k.castSucc) (Lout k.succ) Mt
      (hrealize k.castSucc).2.1 (hrealize k.succ).2.2.1 hMt q u

/-- Apply the analytic localizer construction to the literal buffered-mask
conclusions returned by terminal protection. The relation may contain every
reflected characteristic and elliptic branch; its diagonal clause supplies
the cross-quantization plateau. The same terminal shoulders supply the final
right defect (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_buffered_chain_localizers
    (a b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∃ Ccross Cterminal : ℕ → ℕ → ℝ,
      (∀ s q, 0 ≤ Ccross s q) ∧ (∀ s q, 0 ≤ Cterminal s q) ∧
      ∀ (N : ℕ) (m : Fin (N+1) → LocalizerSymbol (d+1)),
      ∀ (S : Fin (N+1) → Set (E × E)) (V : Set (E × E))
        (relation : (E × E) → (E × E) → Prop),
      (∀ k, IsBufferedLocalizer (m k) (S k) V) →
      (∀ k, cthickening buffer (tsupport (m k)) ⊆
        (closedBall (0 : E) Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩ V) →
      (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ Hmask l) →
      (∀ k : Fin N, ∀ p ∈ cthickening buffer (tsupport (m k.castSucc)), ∀ z,
        p = z ∨ relation p z → closedBall z buffer ⊆ interior {q | m k.succ q = 1}) →
      (∀ k, cthickening buffer (tsupport (m k)) ⊆ interior {z | mt z = 1}) →
      ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ R Lout : Fin (N+1) → H →L[ℂ] H,
      (∀ k, R k = (Lout k).adjoint ∧
        (∀ u, R k u =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (rightLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lout k u =ᵐ[volume]
          fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (m k) (fun z ↦ (u z).ofLp) y)) ∧
        ‖R k‖ ≤ C0 ∧ ‖Lout k‖ ≤ C0) ∧
      ∀ L : ℝ, 1 ≤ L → L ≤ ρ → ∀ Mt : H →L[ℂ] H,
      (∀ u, Mt u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mt (fun z ↦ (u z).ofLp) y)) →
      ∀ (k : Fin N) (s q : ℕ) (backward : Bool)
        (u : LocalL2 (univ : Set E) (EuclideanSpace ℂ (Fin (d+1)))),
      let G := restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ
      let S := (1-localRetardedOperator MeasurableSet.univ univ (R k.succ)).comp
        (localRetardedOperator MeasurableSet.univ univ (Lout k.castSucc))
      let v := (if backward then S.adjoint else S) u
      let w := (1-localRetardedOperator MeasurableSet.univ univ Mt)
        (localRetardedOperator MeasurableSet.univ univ (R k.castSucc) u)
      (v ∈ G.level s ∧ G.gradeNorm s v ≤
        Ccross s q*ρ^s*L^(s+(d+1+1))*(L/ρ)^q*‖u‖) ∧
      (w ∈ G.level s ∧ G.gradeNorm s w ≤
        Cterminal s q*ρ^(2*(d+1)+s)*L^(s+(d+1+1))*(L/ρ)^q*‖u‖) := by
  obtain ⟨C0,hC0,Ccross,Cterminal,hCcross,hCterminal,hest⟩ :=
    exists_prescribed_nested_localizer_estimates b Rbase Hmask hHmask mt ht htc hbuffer
  refine ⟨C0,hC0,Ccross,Cterminal,hCcross,hCterminal,?_⟩
  intro N m S V relation hbuf hcarrier hjets hlink hterminal ρ hρ
  apply hest N m (fun k ↦ (hbuf k).smooth) (fun k ↦ (hbuf k).compactSupport)
    (fun k ↦ (hbuf k).range) _ hjets _ _ ρ hρ
  · intro k p hp
    have h := (hcarrier k (self_subset_cthickening (tsupport (m k)) hp)).1
    exact ⟨h.1, by simpa only [mem_closedBall, dist_zero_right] using h.2.2⟩
  · intro k p hp
    exact hlink k p (self_subset_cthickening (tsupport (m k.castSucc)) hp) p (Or.inl rfl)
  · intro k p hp
    exact (closedBall_subset_cthickening hp buffer).trans (hterminal k)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
