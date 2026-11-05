module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Algebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Sort

/-!
# Selecting disjoint detecting pairs

The finite-dimensional criterion `app:ch_seed:eq:seed-pair-criterion` in
Step 1 of Proposition `app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

namespace JanetCartan.CubeCarrier

/-- The exact disjoint-pair criterion `app:ch_seed:eq:seed-pair-criterion`. -/
def PairCriterion {n : ℕ} (k s : Euclidean n) (p : Fin 4 ↪ Fin n) : Prop :=
  (s (p 0) + s (p 1) ≠ 0 ∨ s (p 2) + s (p 3) ≠ 0) ∧
  ((k (p 0) + k (p 1) = 0 ∧ k (p 2) + k (p 3) = 0) ∨
    (k (p 0) + k (p 1)) * (k (p 2) + k (p 3)) *
      (k (p 0) + k (p 1) + (k (p 2) + k (p 3))) ≠ 0)

/-- A nonzero pair sum of `k` detects a nonzero kernel vector when all
coordinates are nonzero (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem kernel_pair_sum_ne_zero {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    {a b : Fin n} (hab : k a + k b ≠ 0) : s a + s b ≠ 0 := by
  obtain ⟨C, hC, heq, _⟩ := kernel_eq_smul_reciprocal hk hs hker
  have hformula : s a + s b = C * (k a + k b) / (k a * k b) := by
    rw [heq]
    change C * (k a)⁻¹ + C * (k b)⁻¹ = _
    field_simp [hk a, hk b]
    ring
  rw [hformula]
  exact div_ne_zero (mul_ne_zero hC hab) (mul_ne_zero (hk a) (hk b))

/-- Four positive coordinates give admissible disjoint pairs
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem pairCriterion_of_four_pos {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (p : Fin 4 ↪ Fin n) (hp : ∀ i, 0 < k (p i)) : PairCriterion k s p := by
  have hI : 0 < k (p 0) + k (p 1) := add_pos (hp 0) (hp 1)
  have hJ : 0 < k (p 2) + k (p 3) := add_pos (hp 2) (hp 3)
  exact ⟨Or.inl (kernel_pair_sum_ne_zero hk hs hker (ne_of_gt hI)),
    Or.inr (ne_of_gt (mul_pos (mul_pos hI hJ) (add_pos hI hJ)))⟩

/-- Four negative coordinates give admissible disjoint pairs
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem pairCriterion_of_four_neg {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (p : Fin 4 ↪ Fin n) (hp : ∀ i, k (p i) < 0) : PairCriterion k s p := by
  have hI : k (p 0) + k (p 1) < 0 := add_neg (hp 0) (hp 1)
  have hJ : k (p 2) + k (p 3) < 0 := add_neg (hp 2) (hp 3)
  exact ⟨Or.inl (kernel_pair_sum_ne_zero hk hs hker (ne_of_lt hI)),
    Or.inr (mul_ne_zero (mul_ne_zero (ne_of_lt hI) (ne_of_lt hJ))
      (ne_of_lt (add_neg hI hJ)))⟩

/-- Four zero coordinates, one carrying nonzero stress, can be paired
to satisfy `app:ch_seed:eq:seed-pair-criterion`. -/
theorem pairCriterion_of_four_zeros {n : ℕ} {k s : Euclidean n}
    (p : Fin 4 ↪ Fin n) (hk : ∀ i, k (p i) = 0)
    (hs : ∃ i, s (p i) ≠ 0) : ∃ q : Fin 4 ↪ Fin n, PairCriterion k s q := by
  let q : Fin 4 ↪ Fin n := (Equiv.swap 1 2).toEmbedding.trans p
  let r : Fin 4 ↪ Fin n := (Equiv.swap 1 3).toEmbedding.trans p
  have hq : ∀ i, k (q i) = 0 := fun i ↦ hk _
  have hr : ∀ i, k (r i) = 0 := fun i ↦ hk _
  by_cases hp : PairCriterion k s p
  · exact ⟨p, hp⟩
  by_cases hq' : PairCriterion k s q
  · exact ⟨q, hq'⟩
  refine ⟨r, ?_⟩
  have hp' : s (p 0) + s (p 1) = 0 ∧ s (p 2) + s (p 3) = 0 := by
    simpa [PairCriterion, hk] using hp
  have hq'' : s (p 0) + s (p 2) = 0 ∧ s (p 1) + s (p 3) = 0 := by
    have hqq : s (q 0) + s (q 1) = 0 ∧ s (q 2) + s (q 3) = 0 := by
      simpa [PairCriterion, hq] using hq'
    simpa [q, Equiv.swap_apply_def] using hqq
  refine ⟨?_, Or.inl ⟨by simp [hr], by simp [hr]⟩⟩
  simp only [r, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  norm_num [Equiv.swap_apply_def]
  by_contra h
  push Not at h
  have h0 : s (p 0) = 0 := by linarith [hp'.1, hp'.2, hq''.1, h.1]
  have h1 : s (p 1) = 0 := by linarith [hp'.1]
  have h2 : s (p 2) = 0 := by linarith [hq''.1]
  have h3 : s (p 3) = 0 := by linarith [h.1]
  have hall : ∀ i : Fin 4, s (p i) = 0 := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨i, hi⟩ := hs
  exact hi (hall i)


/-- The pair-selection case with at least four positive coordinates
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_four_pos {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hcard : 4 ≤ (Finset.univ.filter (fun i ↦ 0 < k i)).card) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ 0 < k i)
  let p := (Z.orderEmbOfCardLe hcard).toEmbedding
  refine ⟨p, pairCriterion_of_four_pos hk hs hker p ?_⟩
  intro i
  exact (Finset.mem_filter.mp (Z.orderEmbOfCardLe_mem hcard i)).2

/-- The pair-selection case with at least four negative coordinates
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_four_neg {n : ℕ} {k s : Euclidean n}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hcard : 4 ≤ (Finset.univ.filter (fun i ↦ k i < 0)).card) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ k i < 0)
  let p := (Z.orderEmbOfCardLe hcard).toEmbedding
  refine ⟨p, pairCriterion_of_four_neg hk hs hker p ?_⟩
  intro i
  exact (Finset.mem_filter.mp (Z.orderEmbOfCardLe_mem hcard i)).2

/-- The case of at least four zero coordinates, including automatic selection
of a nonzero stress coordinate (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_four_zeros {n : ℕ} {k s : Euclidean n}
    (hs : s ≠ 0) (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hcard : 4 ≤ (Finset.univ.filter (fun i ↦ k i = 0)).card) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ k i = 0)
  have hZ : 4 ≤ Z.card := hcard
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < Z.card by omega)
  have hz' : k z = 0 := (Finset.mem_filter.mp hz).2
  have hsome : ∃ j, s j ≠ 0 := by
    by_contra h
    push Not at h
    apply hs
    ext j
    exact h j
  obtain ⟨j, hj⟩ := hsome
  have hjk : k j = 0 := by
    by_contra hjk
    exact hj (kernel_supported_on_zeros hker ⟨z, hz'⟩ j hjk)
  have hjZ : j ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩
  have herase : 3 ≤ (Z.erase j).card := by
    rw [Finset.card_erase_of_mem hjZ]
    omega
  obtain ⟨T, hTZ, hT⟩ := Finset.exists_subset_card_eq herase
  have hjT : j ∉ T := fun h ↦ (Finset.mem_erase.mp (hTZ h)).1 rfl
  let U := insert j T
  have hU : U.card = 4 := by simp [U, hjT, hT]
  let p := (U.orderEmbOfFin hU).toEmbedding
  have hpzero : ∀ i, k (p i) = 0 := by
    intro i
    have hi := U.orderEmbOfFin_mem hU i
    rcases Finset.mem_insert.mp hi with h | h
    · exact h ▸ hjk
    · exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hTZ h)).2).2
  have hpstress : ∃ i, s (p i) ≠ 0 := by
    have hjU : j ∈ Set.range (U.orderEmbOfFin hU) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_self j T
    obtain ⟨i, hi⟩ := hjU
    refine ⟨i, ?_⟩
    change s (U.orderEmbOfFin hU i) ≠ 0
    rw [hi]
    exact hj
  exact pairCriterion_of_four_zeros p hpzero hpstress


/-- The all-nonzero pair-selection case in dimensions at least seven, by sign
counting (`app:ch_seed:prop:seed-frozen-menu`, Step 1).
The balanced six-dimensional case requires a separate argument. -/
theorem exists_pairCriterion_of_nonzero_ge_seven {n : ℕ} (hn : 7 ≤ n)
    {k s : Euclidean n} (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i ↦ 0 < k i)
  have hneg : (Finset.univ.filter (fun i ↦ ¬0 < k i)) =
      Finset.univ.filter (fun i ↦ k i < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (hk i))
  rw [hneg, Finset.card_univ, Fintype.card_fin] at hpartition
  by_cases hpos : 4 ≤ (Finset.univ.filter (fun i ↦ 0 < k i)).card
  · exact exists_pairCriterion_of_four_pos hk hs hker hpos
  · exact exists_pairCriterion_of_four_neg hk hs hker (by omega)

end JanetCartan.CubeCarrier
