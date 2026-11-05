module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialBuffers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.FlowTransport

/-!
# A finite radial and initial-state refinement

The frequency cover and compact initial-state cover are chosen together,
before coefficients, charts and requested accuracy. The index is finite and
can be used directly in `exists_uniform_nested_physicalDirectLocalizers`.
Consumer: the full conic interior gap in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic ConicPhase

variable {d : ℕ}

/-- Refine the entire fixed radial band and every possible original inverse
initial state simultaneously. The buffers are actual radial images and
compact pieces of them. The original flow ball and elapsed time are retained
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem exists_finite_radial_chart_buffers
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {γ a b σ r R : ℝ} (hγ : 0 < γ) (ha : 0 < a)
    (hσ : 0 ≤ σ) (hσr : σ < r) (hσR : σ ≤ R) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (hc : ∀ k, 0 < c k)
      (zj : Fin n → RootState (Euclidean d)) (rj Rj : Fin n → ℝ)
      (Uj : Fin n → Set (RootState (Euclidean d))),
      (∀ k,
        c k ∈ Icc a b ∧ 0 < rj k ∧ rj k < Rj k ∧ IsCompact (Uj k) ∧
        Uj k ⊆ closedBall (zj k) (rj k) ∧
        Uj k ⊆ rootRadialEquiv (c k) (hc k).ne' '' closedBall z σ ∧
        Uj k ⊆ rootRadialEquiv (c k) (hc k).ne' '' closedBall z R ∧
        (rootRadialEquiv (c k) (hc k).ne').symm '' closedBall (zj k) (rj k) ⊆
          closedBall z r ∧
        (rootRadialEquiv (c k) (hc k).ne').symm '' ball (zj k) (rj k) ⊆ ball z r ∧
        rootRadialEquiv (c k) (hc k).ne' '' closedBall z R ⊆ closedBall (zj k) (Rj k)) ∧
      (∀ η ∈ radialSectionBand ℓ z.2.2 (γ / 2) a b,
        ∃ k₀ : Fin n, (c k₀)⁻¹ • η ∈ ball z.2.2 γ ∧
          ∀ w ∈ closedBall z σ, ∃ k : Fin n,
            c k = c k₀ ∧ rootRadialEquiv (c k) (hc k).ne' w ∈ Uj k) := by
  classical
  obtain ⟨Λ, hΛ, hcover⟩ := exists_radialSectionBand_refinement ℓ z.2.2 hγ ha (b := b)
  have hpos (s : Λ) : 0 < (s : ℝ) := ha.trans_le (hΛ s s.property).1
  choose N zj rj Rj Uj hK hU hj using
    fun s : Λ ↦ exists_finite_radial_initial_buffers (hpos s) z hσr hσR
  let I := (s : Λ) × Fin (N s)
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, (fun k ↦ (e k).1.val), (fun k ↦ hpos (e k).1),
    (fun k ↦ zj (e k).1 (e k).2), (fun k ↦ rj (e k).1 (e k).2),
    (fun k ↦ Rj (e k).1 (e k).2), (fun k ↦ Uj (e k).1 (e k).2), ?_, ?_⟩
  · intro k
    have hk := hj (e k).1 (e k).2
    exact ⟨hΛ _ (e k).1.property, hk.2.1, hk.2.2.1, hk.2.2.2.2⟩
  · intro η hη
    obtain ⟨s, hs, hlocal⟩ := hcover η hη
    let s' : Λ := ⟨s, hs⟩
    have hpick (w) (hw : w ∈ closedBall z σ) :
        ∃ k : Fin (N s'), rootRadialEquiv s (hpos s').ne' w ∈ Uj s' k := by
      have hm := mem_image_of_mem (rootRadialEquiv s (hpos s').ne') hw
      rw [hU s'] at hm
      exact mem_iUnion.mp hm
    obtain ⟨k₀, _⟩ := hpick z (mem_closedBall_self hσ)
    refine ⟨e.symm ⟨s', k₀⟩, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hlocal
    · intro v hv
      obtain ⟨k, hk⟩ := hpick v hv
      refine ⟨e.symm ⟨s', k⟩, ?_, ?_⟩
      · simp only [Equiv.apply_symm_apply]
      · change (fun t : I ↦ rootRadialEquiv t.1.val (hpos t.1).ne' v ∈ Uj t.1 t.2)
          (e (e.symm ⟨s', k⟩))
        rw [e.apply_symm_apply]
        exact hk

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
