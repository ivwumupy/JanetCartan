module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.RelationGeometry
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.Carriers

/-!
# Uniform annular shoulders for the reflected actual relation

The original section bounds control both endpoints of each branch. Apply the
existing endpoint/diagonal shoulder induction to this explicit union, choosing
all constants before current roots, coefficients and histories.
Consumer: angular protection for the even nested construction in
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- Closed shoulders for every finite-depth mixture of original and reflected
steps share a positive annulus and compact physical carrier. The initial
shoulder remains in the supplied source buffer. Only the original primitive
section, root-value and base estimates are used; the elapsed interval and
physical factors in the actual relation are unchanged
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_reflected_bufferedReachableAt_annular_carrier
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
            (bufferedReachableAt (reflectedProofRelation
              (physicalDirectRelation i h Φ U K W χsource χout Δ)) S t n) ⊆
              B' ×ˢ PhysicalShells.frequencyAnnulus a b := by
  obtain ⟨c₀, hc₀, C₀, _, hbounds⟩ :=
    exists_uniform_reflectedProofRelation_bounds_of_section ℓ η₀ ε G hG
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
  refine ⟨δ, lt_min hs (div_pos hρ (by positivity)), a / 2, half_pos ha,
    b + 1, by linarith, cthickening 1 B, hB.cthickening, self_subset_cthickening _, ?_⟩
  intro t ht htδ
  refine ⟨(cthickening_mono (htδ.trans (min_le_left _ _)) S).trans hsource, ?_⟩
  intro i h Φ U K W χsource χout Δ hprimitive hbase n hn
  have htN : t ≤ ρ / ((N : ℝ) + 1) := htδ.trans (min_le_right _ _)
  have hNt : ((N : ℝ) + 1) * t ≤ ρ := by
    have := (le_div_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mp htN
    nlinarith only [this]
  have hnt : ((n : ℝ) + 1) * t ≤ ρ :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) ht).trans hNt
  apply (cthickening_bufferedReachableAt_subset_of_endpoints
    (E := B ×ˢ PhysicalShells.frequencyAnnulus a b) ?_ ?_ ht n).trans
  · exact cthickening_annular_carrier_subset hB (by positivity)
      (hnt.trans (min_le_right _ _)) (hnt.trans (min_le_left _ _))
  · intro p hp
    exact ⟨hSB p hp, (min_le_right c₀ aS).trans (hlow p hp),
      (hhigh p hp).trans ((le_max_right C₀ bS).trans
        ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩
  · intro p q hpq
    have hfreq := (hbounds i h Φ U K W χsource χout Δ hprimitive p q hpq).2
    exact ⟨(reflectedProofRelation_base_mem_of_root_buffer hbase hpq).2,
      (min_le_left c₀ aS).trans hfreq.1,
      hfreq.2.trans ((le_max_left C₀ bS).trans
        ((le_max_right a (max C₀ bS)).trans (le_add_of_nonneg_right zero_le_one)))⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
