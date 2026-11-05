module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.FiniteSelection
import Mathlib.Tactic.Linarith

/-!
# Pair selection with nonzero coordinates

The balanced sign case in Step 1 of `app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- Failure of pair selection forces every positive-pair/negative-pair sum to
vanish (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem pair_sum_eq_zero_of_no_pairCriterion {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hno : ¬ ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p)
    {a b c d : Fin n} (ha : 0 < k a) (hb : 0 < k b)
    (hc : k c < 0) (hd : k d < 0) (hab : a ≠ b) (hcd : c ≠ d) :
    k a + k b + (k c + k d) = 0 := by
  by_contra hsum
  have hac : a ≠ c := by intro h; rw [h] at ha; linarith
  have had : a ≠ d := by intro h; rw [h] at ha; linarith
  have hbc : b ≠ c := by intro h; rw [h] at hb; linarith
  have hbd : b ≠ d := by intro h; rw [h] at hb; linarith
  let p := embeddingFour a b c d hab hac had hbc hbd hcd
  apply hno
  refine ⟨p, Or.inl (kernel_pair_sum_ne_zero hk hs hker (ne_of_gt (add_pos ha hb))),
    Or.inr ?_⟩
  exact mul_ne_zero (mul_ne_zero (ne_of_gt (add_pos ha hb))
    (ne_of_lt (add_neg hc hd))) hsum

/-- Three positive and three negative coordinates with nonzero total sum admit
pairs (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_three_pos_three_neg {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (p q : Fin 3 ↪ Fin n) (hp : ∀ i, 0 < k (p i)) (hq : ∀ i, k (q i) < 0)
    (hsum : (∑ i, k (p i)) + (∑ i, k (q i)) ≠ 0) :
    ∃ r : Fin 4 ↪ Fin n, PairCriterion k s r := by
  by_contra hno
  have heq (a b c d : Fin 3) (hab : a ≠ b) (hcd : c ≠ d) :=
    pair_sum_eq_zero_of_no_pairCriterion hk hs hker hno
      (hp a) (hp b) (hq c) (hq d) (p.injective.ne hab) (q.injective.ne hcd)
  have h1 := heq 0 1 0 1 (by decide) (by decide)
  have h2 := heq 0 2 0 1 (by decide) (by decide)
  have h3 := heq 1 2 0 1 (by decide) (by decide)
  have h4 := heq 0 1 0 2 (by decide) (by decide)
  have h5 := heq 0 1 1 2 (by decide) (by decide)
  apply hsum
  simp only [Fin.sum_univ_three]
  linarith

/-- The all-nonzero pair-selection theorem in dimensions at least six, including
three positive and three negative entries in dimension six
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_nonzero_ge_six {n : ℕ} (hn : 6 ≤ n)
    {k s : Euclidean n} (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let P := Finset.univ.filter (fun i ↦ 0 < k i)
  let Q := Finset.univ.filter (fun i ↦ k i < 0)
  have hneg : (Finset.univ.filter (fun i ↦ ¬0 < k i)) = Q := by
    ext i
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (hk i))
  have hpartition : P.card + Q.card = n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i ↦ 0 < k i)
    simpa only [hneg, Finset.card_univ, Fintype.card_fin] using h
  by_cases hP : 4 ≤ P.card
  · exact exists_pairCriterion_of_four_pos hk hs hker hP
  by_cases hQ : 4 ≤ Q.card
  · exact exists_pairCriterion_of_four_neg hk hs hker hQ
  have hPc : P.card = 3 := by omega
  have hQc : Q.card = 3 := by omega
  let p := (P.orderEmbOfFin hPc).toEmbedding
  let q := (Q.orderEmbOfFin hQc).toEmbedding
  have hp : ∀ i, 0 < k (p i) := fun i ↦
    (Finset.mem_filter.mp (P.orderEmbOfFin_mem hPc i)).2
  have hq : ∀ i, k (q i) < 0 := fun i ↦
    (Finset.mem_filter.mp (Q.orderEmbOfFin_mem hQc i)).2
  have hpSum : (∑ i, k (p i)) = ∑ i ∈ P, k i := by
    rw [← Finset.sum_map, Finset.map_orderEmbOfFin_univ]
  have hqSum : (∑ i, k (q i)) = ∑ i ∈ Q, k i := by
    rw [← Finset.sum_map, Finset.map_orderEmbOfFin_univ]
  obtain ⟨_, _, _, hsum⟩ := kernel_eq_smul_reciprocal hk hs hker
  apply exists_pairCriterion_of_three_pos_three_neg hk hs hker p q hp hq
  rw [hpSum, hqSum, ← hneg]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ 0 < k i)
    (fun i ↦ k i)) ▸ hsum

end JanetCartan.CubeCarrier
