module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# Common carriers for every finite chain

`exists_uniform_physicalDirectRelation_bounds_of_section` bounds the endpoints
of each actual relation. Here those SAME bounds are combined with the compact
nonzero source to cover every chain, including depth zero and elliptic identity
branches. The original elapsed interval, factor supports and whole-segment
restriction stay in the relation.

The primitive producer is `UniformGeometry.exists_uniform_fieldRoot_conicGeometry`:
its fixed section, transverse balls and root-value bounds give the frequency
constants; its `rootPhysicalPosition` bound gives the base envelope. The actual
finite-family selector must restrict those estimates to its `U` and `K`.
Consumer: `Uniformity`'s common final mask for `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- Both physical endpoint bases lie in the same primitive root-buffer
envelope, in both orientations (`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_base_mem_of_root_buffer
    (i : Fin (d + 1))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W B : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (hbase : ∀ v ∈ U ∪ K, (coordinateSplit i).symm (v.1, v.2.1) ∈ B)
    {backward : Bool} {a b : Euclidean (d + 1) × Euclidean (d + 1)}
    (hab : maskedZeroEnergyRelation (coordinateSplit i) h Φ U K W χsource χout Δ backward a b) :
    (adaptedPhysicalPhaseState (coordinateSplit i) a).1 ∈ B ∧
      (adaptedPhysicalPhaseState (coordinateSplit i) b).1 ∈ B := by
  obtain ⟨vr, hv, hs, ht⟩ := (maskedZeroEnergyRelation_iff_accepted _ _ _ _ _ _ _ _ _ _ _ _).1 hab
  have hsource := hbase vr.1 (Or.inl hv.1.1)
  have htarget := hbase (Φ vr) (Or.inr (by
    simpa only [one_mul] using (hv.2.1 1 (by simp)).1))
  cases backward
  · change a = _ at hs
    change b = _ at ht
    simpa only [hs, ht, adaptedPhysicalPhaseState_rootSuspensionState,
      physicalPencilRootState] using ⟨hsource, htarget⟩
  · change b = _ at hs
    change a = _ at ht
    simpa only [hs, ht, adaptedPhysicalPhaseState_rootSuspensionState,
      physicalPencilRootState] using ⟨htarget, hsource⟩

private theorem chain_mem_of_endpoints
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {P : (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hR : ∀ p q, R p q → P q)
    {p q : Euclidean (d + 1) × Euclidean (d + 1)} {n : ℕ}
    (hc : PositiveConicChain R p q n) (hp : P p) : P q := by
  induction hc with
  | refl p => exact hp
  | tail hs _ ih =>
    apply ih
    rcases hs with rfl | hs
    · exact hp
    · exact hR _ _ hs

/-- Common positive lower and finite upper frequency endpoints for all
finite depths are chosen before any root, flow, factor mask or current field.
The source contributes its own annular bounds so depth zero and all-diagonal
chains are included. The section and base inputs are literal restrictions of
`UniformGeometry/Construction`'s fixed-buffer estimates, not estimates of an
already constructed chain (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_reachableAt_annular_carrier_of_section
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hS : IsCompact S) (hne : ∀ p ∈ S, p.2 ≠ 0)
    {B : Set (Euclidean (d + 1))} (hSB : ∀ p ∈ S, p.1 ∈ B) :
    ∃ a > (0 : ℝ), ∃ b > a,
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ),
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (ε j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j → (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        ∀ n, reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S n ⊆
          B ×ˢ PhysicalShells.frequencyAnnulus a b := by
  obtain ⟨c₀, hc₀, C₀, _, hb⟩ :=
    exists_uniform_physicalDirectRelation_bounds_of_section ℓ η₀ ε G hG
  obtain ⟨aS, haS, hlow⟩ := CompatibleResponse.exists_uniform_positive_bound hS
    continuous_snd.norm.continuousOn (fun p hp ↦ norm_pos_iff.mpr (hne p hp))
  obtain ⟨bS, hhigh⟩ := hS.exists_bound_of_continuousOn continuous_snd.continuousOn
  let a := min c₀ aS
  let b := max a (max C₀ bS) + 1
  refine ⟨a, lt_min hc₀ haS, b, ?_, ?_⟩
  · exact (le_max_left a (max C₀ bS)).trans_lt (lt_add_one _)
  · intro i h Φ U K W χsource χout Δ hprimitive hbase n q hq
    obtain ⟨p, hp, hc⟩ := hq
    apply chain_mem_of_endpoints (P := fun p ↦ p ∈ B ×ˢ PhysicalShells.frequencyAnnulus a b)
      (R := physicalDirectRelation i h Φ U K W χsource χout Δ) ?_ hc
    · exact ⟨hSB p hp, (min_le_right c₀ aS).trans (hlow p hp),
        (hhigh p hp).trans ((le_max_right C₀ bS).trans
          ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩
    · intro p q hpq
      have hfreq := (hb i h Φ U K W χsource χout Δ hprimitive p q hpq).2
      obtain ⟨j, backward, u, v, huv, rfl, rfl⟩ := hpq
      exact ⟨(maskedZeroEnergyRelation_base_mem_of_root_buffer (i j) (hbase j) huv).2,
        (min_le_left c₀ aS).trans hfreq.1,
        hfreq.2.trans ((le_max_left C₀ bS).trans
          ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
