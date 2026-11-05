module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.NonzeroSelection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The nonexceptional five-dimensional selection in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- Pair admissibility is invariant under reversing `k`, as used in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem pairCriterion_neg_left {n : ℕ} {k s : Euclidean n} (p : Fin 4 ↪ Fin n) :
    PairCriterion (-k) s p ↔ PairCriterion k s p := by
  simp only [PairCriterion, PiLp.neg_apply, ← neg_add, mul_neg, neg_mul, neg_neg,
    ne_eq, neg_eq_zero]

/-- Reversing the covector preserves its kernel
(`app:ch_seed:eq:seed-kernel-pair`). -/
theorem kernel_neg_left {n : ℕ} {k s : Euclidean n}
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    (cubePencil (-k)).mulVec (fun i ↦ s i) = 0 := by
  rw [pencil_mulVec_eq_zero_iff] at hker ⊢
  intro i
  simp only [PiLp.neg_apply, Finset.sum_neg_distrib, mul_neg, neg_mul]
  exact congrArg Neg.neg (hker i)

/-- The quadratic stress vector is even
(`app:ch_seed:prop:seed-frozen-menu`). -/
theorem quadratic_neg {n : ℕ} (k : Euclidean n) : quadratic (-k) = quadratic k := by
  ext i
  simp [quadratic, PiLp.neg_apply]

/-- The five-dimensional reciprocal constraint
`app:ch_seed:eq:seed-five-reciprocal` follows from a nonzero kernel vector. -/
theorem sum_mul_reciprocal_of_kernel_five {k s : Euclidean 5}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    (∑ i, k i) * (∑ i, reciprocal k i) = 1 := by
  obtain ⟨C, hC, heq, _⟩ := kernel_eq_smul_reciprocal hk hs hker
  have h := (pencil_mulVec_eq_zero_iff k s).mp hker 0
  rw [heq] at h
  simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
  have hleft : k 0 * (C * reciprocal k 0) = C := by
    simp [mul_left_comm, hk 0]
  rw [hleft] at h
  norm_num [cubeCoefficient] at h
  have : C * ((∑ i, k i) * (∑ i, reciprocal k i)) = C * 1 := by
    simp only [reciprocal_apply]
    nlinarith [h]
  exact mul_left_cancel₀ hC this

/-- The scalar calculation isolating the node pattern from the three failed
positive pairs (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem five_node_values_of_pair_sums {a b c u v : ℝ}
    (ha : 0 < a) (hu : u < 0) (hv : v < 0)
    (hab : a + b + (u + v) = 0)
    (hac : a + c + (u + v) = 0)
    (hbc : b + c + (u + v) = 0)
    (hrec : (a+b+c+u+v) * (a⁻¹+b⁻¹+c⁻¹+u⁻¹+v⁻¹) = 1) :
    b = a ∧ c = a ∧ u = -a ∧ v = -a := by
  have hb : b = a := by linarith
  have hc : c = a := by linarith
  have hsum : u + v = -2*a := by linarith
  have htotal : a+b+c+u+v = a := by linarith
  rw [htotal, hb, hc] at hrec
  have ha0 := ne_of_gt ha
  have hu0 := ne_of_lt hu
  have hv0 := ne_of_lt hv
  have heq : 3 - 2*a^2/(u*v) = 1 := by
    calc
      _ = a * (3/a + (u+v)/(u*v)) := by
        rw [hsum]
        field_simp [ha0, hu0, hv0]
        ring
      _ = a * (a⁻¹+a⁻¹+a⁻¹+u⁻¹+v⁻¹) := by
        field_simp [ha0, hu0, hv0]
        ring
      _ = 1 := hrec
  have hprod : u*v = a^2 := by
    field_simp [hu0, hv0] at heq
    nlinarith
  have huval : u = -a := by
    nlinarith [sq_nonneg (u+a), sq_nonneg (u+v+2*a)]
  exact ⟨hb, hc, huval, by linarith⟩

/-- With three positive entries, failure of pair selection forces a common
quadratic zero (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem quadratic_eq_zero_of_no_pairCriterion_five_three_pos {k s : Euclidean 5}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hno : ¬ ∃ p : Fin 4 ↪ Fin 5, PairCriterion k s p)
    (hPc : (Finset.univ.filter (fun i ↦ 0 < k i)).card = 3) : quadratic k = 0 := by
  let P := Finset.univ.filter (fun i ↦ 0 < k i)
  let Q := Finset.univ.filter (fun i ↦ k i < 0)
  change P.card = 3 at hPc
  have hneg : (Finset.univ.filter (fun i ↦ ¬0 < k i)) = Q := by
    ext i
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (hk i))
  have hQc : Q.card = 2 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5))) (fun i ↦ 0 < k i)
    change P.card + _ = _ at h
    rw [hPc, hneg] at h
    norm_num only [Finset.card_univ, Fintype.card_fin] at h
    omega
  let p := (P.orderEmbOfFin hPc).toEmbedding
  let q := (Q.orderEmbOfFin hQc).toEmbedding
  have hp : ∀ i, 0 < k (p i) := fun i ↦
    (Finset.mem_filter.mp (P.orderEmbOfFin_mem hPc i)).2
  have hq : ∀ i, k (q i) < 0 := fun i ↦
    (Finset.mem_filter.mp (Q.orderEmbOfFin_mem hQc i)).2
  have hsum (f : Fin 5 → ℝ) : (∑ i, f (p i)) + (∑ i, f (q i)) = ∑ i, f i := by
    have hpSum : (∑ i, f (p i)) = ∑ i ∈ P, f i := by
      rw [← Finset.sum_map, Finset.map_orderEmbOfFin_univ]
    have hqSum : (∑ i, f (q i)) = ∑ i ∈ Q, f i := by
      rw [← Finset.sum_map, Finset.map_orderEmbOfFin_univ]
    rw [hpSum, hqSum, ← hneg]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ 0 < k i) f
  have heq (a b : Fin 3) (hab : a ≠ b) :=
    pair_sum_eq_zero_of_no_pairCriterion hk hs hker hno
      (hp a) (hp b) (hq 0) (hq 1) (p.injective.ne hab) (q.injective.ne (by decide))
  have hrec := sum_mul_reciprocal_of_kernel_five hk hs hker
  rw [← hsum (fun i ↦ k i), ← hsum (fun i ↦ reciprocal k i)] at hrec
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, reciprocal_apply] at hrec
  obtain ⟨hb, hc, hu, hv⟩ := five_node_values_of_pair_sums (hp 0) (hq 0) (hq 1)
    (heq 0 1 (by decide)) (heq 0 2 (by decide)) (heq 1 2 (by decide))
    (by simpa only [add_assoc] using hrec)
  have hpval : ∀ j, k (p j) = k (p 0) := by
    intro j
    fin_cases j
    · rfl
    · exact hb
    · exact hc
  have hqval : ∀ j, k (q j) = -k (p 0) := by
    intro j
    fin_cases j
    · exact hu
    · exact hv
  have hsumk : (∑ i, k i) = k (p 0) := by
    rw [← hsum (fun i ↦ k i)]
    simp only [Fin.sum_univ_three, Fin.sum_univ_two, hpval, hqval]
    ring
  ext i
  have hival : k i = k (p 0) ∨ k i = -k (p 0) := by
    rcases lt_or_gt_of_ne (hk i) with hi | hi
    · have hmem : i ∈ Set.range (Q.orderEmbOfFin hQc) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      obtain ⟨j, hj⟩ := hmem
      exact Or.inr (hj ▸ hqval j)
    · have hmem : i ∈ Set.range (P.orderEmbOfFin hPc) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      obtain ⟨j, hj⟩ := hmem
      exact Or.inl (hj ▸ hpval j)
  change k i ^ 2 - cubeCoefficient 5 * (∑ j, k j) ^ 2 = 0
  rw [hsumk]
  rcases hival with hi | hi <;> norm_num [cubeCoefficient, hi]

/-- Every all-nonzero five-dimensional direction with nonzero quadratic stress
admits pairs (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_nonzero_five {k s : Euclidean 5}
    (hk : ∀ i, k i ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hq : quadratic k ≠ 0) : ∃ p : Fin 4 ↪ Fin 5, PairCriterion k s p := by
  by_contra hno
  let P := Finset.univ.filter (fun i ↦ 0 < k i)
  let Q := Finset.univ.filter (fun i ↦ k i < 0)
  have hneg : (Finset.univ.filter (fun i ↦ ¬0 < k i)) = Q := by
    ext i
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (hk i))
  have hpartition : P.card + Q.card = 5 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5))) (fun i ↦ 0 < k i)
    simpa only [hneg, Finset.card_univ, Fintype.card_fin] using h
  have hP : P.card < 4 := by
    by_contra h
    exact hno (exists_pairCriterion_of_four_pos hk hs hker (show 4 ≤ P.card by omega))
  have hQ : Q.card < 4 := by
    by_contra h
    exact hno (exists_pairCriterion_of_four_neg hk hs hker (show 4 ≤ Q.card by omega))
  by_cases hPc : P.card = 3
  · exact hq (quadratic_eq_zero_of_no_pairCriterion_five_three_pos hk hs hker hno hPc)
  · have hkneg : ∀ i, (-k) i ≠ 0 := fun i ↦ neg_ne_zero.mpr (hk i)
    have hnoNeg : ¬ ∃ p : Fin 4 ↪ Fin 5, PairCriterion (-k) s p := by
      rintro ⟨p, hp⟩
      exact hno ⟨p, (pairCriterion_neg_left p).mp hp⟩
    have hPneg : (Finset.univ.filter (fun i ↦ 0 < (-k) i)).card = 3 := by
      change (Finset.univ.filter (fun i ↦ 0 < -k i)).card = 3
      simp only [neg_pos]
      change Q.card = 3
      omega
    apply hq
    rw [← quadratic_neg k]
    exact quadratic_eq_zero_of_no_pairCriterion_five_three_pos hkneg hs
      (kernel_neg_left hker) hnoNeg hPneg

end JanetCartan.CubeCarrier
