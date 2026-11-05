module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Shoulders
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ReachableBounds

/-!
# Uniform compact and annular carriers for closed shoulders

The primitive section, transverse ball and root-value estimates bound every
endpoint of the actual physical relation. A relation step returns to this fixed
envelope; a diagonal step adds only the chosen shoulder width. Consequently a
single width controls all closed shoulders through any fixed finite depth.

The consumer is the nested-mask assembly for `app:ch_regular:lem:finite-chain`.
This supplies its base, frequency and initial-source bounds. The final angular
protection requires a separate uniform comparison argument.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- If the source and all relation targets lie in one envelope, the closed
shoulder at depth `n` lies within `(n + 1) * δ` of that envelope. The full
diagonal is included. `exists_uniform_bufferedReachableAt_annular_carrier_of_section`
instantiates the endpoint condition from primitive root bounds
(`app:ch_regular:lem:finite-chain`). -/
theorem cthickening_bufferedReachableAt_subset_of_endpoints
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {S E : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hSE : S ⊆ E) (hR : ∀ p q, R p q → q ∈ E)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    cthickening δ (bufferedReachableAt R S δ n) ⊆
      cthickening (((n : ℝ) + 1) * δ) E := by
  have hreach : ∀ k : ℕ, bufferedReachableAt R S δ k ⊆
      cthickening ((k : ℝ) * δ) E := by
    intro k
    induction k with
    | zero =>
      exact hSE.trans (self_subset_cthickening _)
    | succ k ih =>
      rintro q ⟨p, hp, hc⟩
      cases hc with
      | tail hs hc =>
        cases hc
        rcases hs with rfl | hs
        · have hp' := cthickening_cthickening_subset hδ
            (mul_nonneg (Nat.cast_nonneg k) hδ) E
            (cthickening_subset_of_subset δ ih hp)
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hp'
        · exact self_subset_cthickening _ (hR _ _ hs)
  have hsub := (cthickening_subset_of_subset δ (hreach n)).trans
    (cthickening_cthickening_subset hδ (mul_nonneg (Nat.cast_nonneg n) hδ) E)
  simpa only [add_mul, one_mul, add_comm] using hsub

/-- A small closed shoulder of a compact physical annular carrier remains
in a fixed enlarged compact base carrier and a positive frequency annulus.
This is the metric estimate used by the finite-depth uniform construction
(`app:ch_regular:lem:finite-chain`). -/
theorem cthickening_annular_carrier_subset
    {B : Set (Euclidean (d + 1))} (hB : IsCompact B)
    {a b t : ℝ} (ht : 0 ≤ t) (hta : t ≤ a / 2) (ht1 : t ≤ 1) :
    cthickening t (B ×ˢ PhysicalShells.frequencyAnnulus (n := d + 1) a b) ⊆
      cthickening 1 B ×ˢ PhysicalShells.frequencyAnnulus (a / 2) (b + 1) := by
  intro q hq
  rw [(hB.prod (PhysicalShells.isCompact_frequencyAnnulus a b)).cthickening_eq_biUnion_closedBall ht]
    at hq
  obtain ⟨p, hp, hpq⟩ := mem_iUnion₂.mp hq
  have hdist : dist q p ≤ t := hpq
  have hx : dist q.1 p.1 ≤ t := (le_max_left _ _).trans hdist
  have hξ : dist q.2 p.2 ≤ t := (le_max_right _ _).trans hdist
  refine ⟨mem_cthickening_of_dist_le _ _ _ _ hp.1 (hx.trans ht1), ?_, ?_⟩
  · have hnorm := norm_sub_norm_le p.2 q.2
    rw [← dist_eq_norm, dist_comm] at hnorm
    have hlo := hp.2.1
    linarith
  · have hnorm := norm_sub_norm_le q.2 p.2
    rw [← dist_eq_norm] at hnorm
    have hhi := hp.2.2
    linarith

/-- A positive width, common compact base and positive annular endpoints are
chosen before the current roots, flows, physical factor masks and coefficients.
They control EVERY closed shoulder through depth `N`, including all-diagonal
chains and depth zero, and keep the initial shoulder in its prescribed source
buffer. Every smaller nonnegative width has the same bounds, so the angular
protection construction can shrink the width without repeating this argument.

The primitive estimates are literal restrictions of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry` to its selected
initial and whole-segment buffers. The parent selects that finite family.
Both orientations, all physical factor supports, whole segments, and the
original elapsed bound are retained in `physicalDirectRelation`. This proves
the base/frequency part of `app:ch_regular:lem:finite-chain`; it does not assert
the remaining angular protection. -/
theorem exists_uniform_bufferedReachableAt_annular_carrier_of_section
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hS : IsCompact S) (hne : ∀ p ∈ S, p.2 ≠ 0)
    {B : Set (Euclidean (d + 1))} (hB : IsCompact B) (hSB : ∀ p ∈ S, p.1 ∈ B)
    {Bsource : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hBsource : IsOpen Bsource) (hSBsource : S ⊆ Bsource) (N : ℕ) :
    ∃ δ > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > a,
      ∃ B' : Set (Euclidean (d + 1)), IsCompact B' ∧ B ⊆ B' ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ →
        cthickening t S ⊆ Bsource ∧
        ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
          (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
          (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
          (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ),
          (∀ j v, v ∈ U j ∪ K j →
            v.2.2 ∈ closedBall (η₀ j) (ε j) ∧
            (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
          (∀ j v, v ∈ U j ∪ K j →
            (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
          ∀ n ≤ N, cthickening t
            (bufferedReachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S t n) ⊆
              B' ×ˢ PhysicalShells.frequencyAnnulus a b := by
  obtain ⟨c₀, hc₀, C₀, _, hbounds⟩ :=
    exists_uniform_physicalDirectRelation_bounds_of_section ℓ η₀ ε G hG
  obtain ⟨aS, haS, hlow⟩ := CompatibleResponse.exists_uniform_positive_bound hS
    continuous_snd.norm.continuousOn (fun p hp ↦ norm_pos_iff.mpr (hne p hp))
  obtain ⟨bS, hhigh⟩ := hS.exists_bound_of_continuousOn continuous_snd.continuousOn
  obtain ⟨s, hs, hsource⟩ := hS.exists_cthickening_subset_open hBsource hSBsource
  let a := min c₀ aS
  let b := max a (max C₀ bS) + 1
  have ha : 0 < a := lt_min hc₀ haS
  have hab : a < b := (le_max_left a (max C₀ bS)).trans_lt (lt_add_one _)
  let ρ := min 1 (a / 2)
  have hρ : 0 < ρ := lt_min zero_lt_one (half_pos ha)
  let δ := min s (ρ / ((N : ℝ) + 1))
  have hδ : 0 < δ := lt_min hs (div_pos hρ (by positivity))
  refine ⟨δ, hδ, a / 2, half_pos ha, b + 1, by linarith, cthickening 1 B,
    hB.cthickening, self_subset_cthickening _, ?_⟩
  intro t ht htδ
  refine ⟨(cthickening_mono (htδ.trans (min_le_left _ _)) S).trans hsource, ?_⟩
  intro i h Φ U K W χsource χout Δ hprimitive hbase n hn
  have hnt : ((n : ℝ) + 1) * t ≤ ρ := by
    have htN : t ≤ ρ / ((N : ℝ) + 1) := htδ.trans (min_le_right _ _)
    have hNt : ((N : ℝ) + 1) * t ≤ ρ := by
      have := (le_div_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mp htN
      nlinarith only [this]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) ht).trans hNt
  apply (cthickening_bufferedReachableAt_subset_of_endpoints
    (E := B ×ˢ PhysicalShells.frequencyAnnulus a b) ?_ ?_ ht n).trans
  · apply cthickening_annular_carrier_subset hB (by positivity)
    · exact hnt.trans (min_le_right _ _)
    · exact hnt.trans (min_le_left _ _)
  · intro p hp
    exact ⟨hSB p hp, (min_le_right c₀ aS).trans (hlow p hp),
      (hhigh p hp).trans ((le_max_right C₀ bS).trans
        ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩
  · intro p q hpq
    have hfreq := (hbounds i h Φ U K W χsource χout Δ hprimitive p q hpq).2
    obtain ⟨j, backward, u, v, huv, rfl, rfl⟩ := hpq
    exact ⟨(maskedZeroEnergyRelation_base_mem_of_root_buffer (i j) (hbase j) huv).2,
      (min_le_left c₀ aS).trans hfreq.1,
      hfreq.2.trans ((le_max_left C₀ bS).trans
        ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
