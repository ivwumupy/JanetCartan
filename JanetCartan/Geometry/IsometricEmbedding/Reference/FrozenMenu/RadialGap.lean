module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.ChordEstimates

/-!
# Radial labels preserve the bad-subspace gap

Step 4 of `app:ch_seed:prop:seed-frozen-menu`: apply the checked radial
domination theorem to a family with uniform norm and regular-direction bounds.
The geometric construction of that family remains a separate obligation.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- The bad set is a union of linear subspaces, so its directional gap is
unchanged by reversing a carrier (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem BadDirectionGap.neg {n : ℕ} {x : Euclidean n} {γ : ℝ}
    (h : BadDirectionGap γ x) : BadDirectionGap γ (-x) := by
  intro L hL
  simpa only [NormedSpace.normalize_neg, map_neg, norm_neg] using h L hL

/-- Fixed radial labels separate both cross-group signs from every bad
subspace (`app:ch_seed:prop:seed-frozen-menu`, item 3). The parameters may
include several patches in the same group, and duplicate specifications keep
their separate indices. No sample-spacing parameter enters the labels. -/
theorem exists_radial_badDirectionGap {n : ℕ} {ι : Type*} [Finite ι]
    {Z : ι → Type*} (ξ : (i : ι) → Z i → Euclidean n) {a b γ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hγ : 0 < γ)
    (hnorm : ∀ i z, a ≤ ‖ξ i z‖ ∧ ‖ξ i z‖ ≤ b)
    (hgap : ∀ i z, BadDirectionGap γ (ξ i z)) :
    ∃ R : ι → ℝ, (∀ i, 1 ≤ R i) ∧ Function.Injective R ∧
      ∀ i j, i ≠ j → ∀ (z : Z i) (w : Z j),
        R i • ξ i z - R j • ξ j w ≠ 0 ∧
        BadDirectionGap (γ / 2) (R i • ξ i z - R j • ξ j w) ∧
        R i • ξ i z + R j • ξ j w ≠ 0 ∧
        BadDirectionGap (γ / 2) (R i • ξ i z + R j • ξ j w) := by
  obtain ⟨R, δ, hR, hinj, hδ, hsep⟩ :=
    exists_stable_radial_separation (E := Euclidean n) ι ha hb (half_pos hγ)
  refine ⟨R, hR, hinj, ?_⟩
  intro i j hij z w
  have hm := hsep i j hij (ξ i z) (ξ j w) (ξ i z) (ξ j w) 1 (-1)
    (hnorm i z).1 (hnorm i z).2 (hnorm j w).1 (hnorm j w).2
    (by simpa using hδ.le) (by simpa using hδ.le) (by norm_num) (by norm_num)
  have hp := hsep i j hij (ξ i z) (ξ j w) (ξ i z) (ξ j w) 1 1
    (hnorm i z).1 (hnorm i z).2 (hnorm j w).1 (hnorm j w).2
    (by simpa using hδ.le) (by simpa using hδ.le) (by norm_num) (by norm_num)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at hm hp
  have hpos : 0 < a / 2 * max (R i) (R j) := by
    apply mul_pos (half_pos ha)
    exact zero_lt_one.trans_le ((hR i).trans (le_max_left _ _))
  refine ⟨norm_pos_iff.mp (hpos.trans_le hm.1), ?_,
    norm_pos_iff.mp (hpos.trans_le hp.1), ?_⟩
  · rcases lt_or_gt_of_ne (hinj.ne hij) with h | h
    · convert (hgap j w).neg.of_normalize_close (hm.2.2.1 h) using 1
      ring
    · convert (hgap i z).of_normalize_close (hm.2.2.2 h) using 1
      ring
  · rcases lt_or_gt_of_ne (hinj.ne hij) with h | h
    · convert (hgap j w).of_normalize_close (hp.2.2.1 h) using 1
      ring
    · convert (hgap i z).of_normalize_close (hp.2.2.2 h) using 1
      ring

end JanetCartan.FrozenMenu
