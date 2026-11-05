module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.FiniteSelection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Pair selection in the presence of zero coordinates

The zero-coordinate cases of `app:ch_seed:prop:seed-frozen-menu`, Step 1.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- A nonzero kernel vector has nonzero stress on a zero coordinate of `k`
(`app:ch_seed:eq:seed-kernel-pair`). -/
theorem exists_nonzero_stress_on_zero {n : ℕ} {k s : Euclidean n}
    (hs : s ≠ 0) (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hz : ∃ i, k i = 0) : ∃ i, k i = 0 ∧ s i ≠ 0 := by
  have hex : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (by ext i; exact h i)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, by by_contra h; exact hi (kernel_supported_on_zeros hker hz i h), hi⟩

/-- Two zero coordinates and two nonzero coordinates with nonzero sum give
mixed detecting pairs (`app:ch_seed:eq:seed-pair-criterion`). -/
theorem exists_pairCriterion_of_mixed_pairs {n : ℕ} {k s : Euclidean n}
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    {z w a b : Fin n} (hz : k z = 0) (hw : k w = 0) (hzw : z ≠ w)
    (ha : k a ≠ 0) (hb : k b ≠ 0) (hab : a ≠ b)
    (hsz : s z ≠ 0) (hsum : k a + k b ≠ 0) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  have hza : z ≠ a := fun h ↦ ha (h ▸ hz)
  have hzb : z ≠ b := fun h ↦ hb (h ▸ hz)
  have hwa : w ≠ a := fun h ↦ ha (h ▸ hw)
  have hwb : w ≠ b := fun h ↦ hb (h ▸ hw)
  let p := embeddingFour z a w b hza hzw hzb hwa.symm hab hwb
  refine ⟨p, ?_⟩
  have hsa := kernel_supported_on_zeros hker ⟨z, hz⟩ a ha
  change (s z + s a ≠ 0 ∨ s w + s b ≠ 0) ∧ _
  refine ⟨Or.inl (by simpa [hsa] using hsz), Or.inr ?_⟩
  change (k z + k a) * (k w + k b) * (k z + k a + (k w + k b)) ≠ 0
  simpa [hz, hw] using mul_ne_zero (mul_ne_zero ha hb) hsum

/-- Two or more zeros and three or more nonzeros admit detecting pairs
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_two_zeros_three_nonzeros {n : ℕ} {k s : Euclidean n}
    (hs : s ≠ 0) (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hZ : 2 ≤ (Finset.univ.filter (fun i ↦ k i = 0)).card)
    (hN : 3 ≤ (Finset.univ.filter (fun i ↦ k i ≠ 0)).card) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ k i = 0)
  let N := Finset.univ.filter (fun i ↦ k i ≠ 0)
  change _ ≤ Z.card at hZ
  change _ ≤ N.card at hN
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < Z.card by omega)
  obtain ⟨z, hz, hsz⟩ := exists_nonzero_stress_on_zero hs hker
    ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hzZ : z ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (Z.erase z).card by
    rw [Finset.card_erase_of_mem hzZ]; omega)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
  obtain ⟨a, ha, b, hb, hab, hsum⟩ := exists_pair_sum_ne_zero k N hN
    ⟨j, hj, (Finset.mem_filter.mp hj).2⟩
  exact exists_pairCriterion_of_mixed_pairs hker hz
    (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).2
    (Finset.mem_erase.mp hw).1.symm (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp hb).2 hab hsz hsum

/-- Three or more zeros and at least two nonzeros admit detecting pairs, including
opposite nonzero entries (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_three_zeros_two_nonzeros {n : ℕ} {k s : Euclidean n}
    (hs : s ≠ 0) (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hZ : 3 ≤ (Finset.univ.filter (fun i ↦ k i = 0)).card)
    (hN : 2 ≤ (Finset.univ.filter (fun i ↦ k i ≠ 0)).card) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ k i = 0)
  let N := Finset.univ.filter (fun i ↦ k i ≠ 0)
  change _ ≤ Z.card at hZ
  change _ ≤ N.card at hN
  let q := N.orderEmbOfCardLe hN
  let a := q 0
  let b := q 1
  have ha : k a ≠ 0 := (Finset.mem_filter.mp (N.orderEmbOfCardLe_mem hN 0)).2
  have hb : k b ≠ 0 := (Finset.mem_filter.mp (N.orderEmbOfCardLe_mem hN 1)).2
  have hab : a ≠ b := fun h ↦ (by norm_num : (0 : Fin 2) ≠ 1) (q.injective h)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < Z.card by omega)
  obtain ⟨z, hz, hsz⟩ := exists_nonzero_stress_on_zero hs hker
    ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hzZ : z ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  by_cases hsum : k a + k b ≠ 0
  · obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (Z.erase z).card by
      rw [Finset.card_erase_of_mem hzZ]; omega)
    exact exists_pairCriterion_of_mixed_pairs hker hz
      (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).2
      (Finset.mem_erase.mp hw).1.symm ha hb hab hsz hsum
  · obtain ⟨u, hu, v, hv, huv, hsuv⟩ := exists_pair_sum_ne_zero s Z hZ ⟨z, hzZ, hsz⟩
    have hku : k u = 0 := (Finset.mem_filter.mp hu).2
    have hkv : k v = 0 := (Finset.mem_filter.mp hv).2
    let p := embeddingFour u v a b huv
      (fun h ↦ ha (h ▸ hku)) (fun h ↦ hb (h ▸ hku))
      (fun h ↦ ha (h ▸ hkv)) (fun h ↦ hb (h ▸ hkv)) hab
    refine ⟨p, Or.inl hsuv, Or.inl ?_⟩
    change k u + k v = 0 ∧ k a + k b = 0
    exact ⟨by simp [hku, hkv], not_ne_iff.mp hsum⟩

/-- A unique zero coordinate admits detecting pairs in every dimension at least
five (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pairCriterion_of_unique_zero {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    {z : Fin n} (hz : k z = 0) (hunique : ∀ i, k i = 0 → i = z) :
    ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  have hnon (i : Fin n) (hi : i ≠ z) : k i ≠ 0 := fun h ↦ hi (hunique i h)
  have hsupport (i : Fin n) (hi : i ≠ z) : s i = 0 :=
    kernel_supported_on_zeros hker ⟨z, hz⟩ i (hnon i hi)
  obtain ⟨j, hj, hsj⟩ := exists_nonzero_stress_on_zero hs hker ⟨z, hz⟩
  have hsz : s z ≠ 0 := hunique j hj ▸ hsj
  have hsum_s : (∑ i, s i) = s z := Finset.sum_eq_single z
    (fun i _ hi ↦ hsupport i hi) (by simp)
  have hcoef : cubeCoefficient n ≠ 0 := by
    have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_ne_zero (pow_ne_zero 2 (by linarith))
  have hsum_k : (∑ i, k i) = 0 := by
    have h := (pencil_mulVec_eq_zero_iff k s).mp hker z
    rw [hz, zero_mul, hsum_s] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hsz)).resolve_left hcoef
  let N := Finset.univ.erase z
  have hN : 4 ≤ N.card := by simp [N]; omega
  have hNz (i : Fin n) : i ∈ N ↔ i ≠ z := by simp [N]
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < N.card by omega)
  obtain ⟨a, ha, b, hb, hab, hsum⟩ := exists_pair_sum_ne_zero k N (by omega)
    ⟨i, hi, hnon i ((hNz i).mp hi)⟩
  let T := (N.erase a).erase b
  have hb' : b ∈ N.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hT : 2 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    omega
  have hsum_N : (∑ i ∈ N, k i) = 0 := by
    simp [N, hz, hsum_k]
  have hex : ∃ c ∈ T, k a + k b + k c ≠ 0 := by
    by_contra h
    push Not at h
    have hval : ∀ c ∈ T, k c = -(k a + k b) := by
      intro c hc
      linarith [h c hc]
    have hsumT : (∑ c ∈ T, k c) = (T.card : ℝ) * -(k a + k b) := by
      rw [Finset.sum_congr rfl hval]
      simp only [Finset.sum_const, nsmul_eq_mul]
    have h1 := Finset.sum_erase_add N (fun i ↦ k i) ha
    have h2 := Finset.sum_erase_add (N.erase a) (fun i ↦ k i) hb'
    change (∑ i ∈ T, k i) + k b = _ at h2
    have heq : ((T.card : ℝ) - 1) * (k a + k b) = 0 := by
      rw [hsumT] at h2
      rw [hsum_N] at h1
      linarith
    have hcount : (2 : ℝ) ≤ T.card := by exact_mod_cast hT
    exact hsum ((mul_eq_zero.mp heq).resolve_left (by linarith))
  obtain ⟨c, hc, habc⟩ := hex
  have hc' := Finset.mem_erase.mp hc
  have hc'' := Finset.mem_erase.mp hc'.2
  have haz := (hNz a).mp ha
  have hbz := (hNz b).mp hb
  have hcz := (hNz c).mp hc''.2
  let p := embeddingFour a b z c hab haz hc''.1.symm hbz hc'.1.symm hcz.symm
  refine ⟨p, Or.inr ?_, Or.inr ?_⟩
  · change s z + s c ≠ 0
    simpa [hsupport c hcz] using hsz
  · change (k a + k b) * (k z + k c) * (k a + k b + (k z + k c)) ≠ 0
    simpa [hz] using mul_ne_zero (mul_ne_zero hsum (hnon c hcz)) habc


/-- All zero-coordinate cases of pair selection, with the exact `n ≥ 5`
hypothesis of `app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem exists_pairCriterion_of_zero_coordinate {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hz : ∃ i, k i = 0) : ∃ p : Fin 4 ↪ Fin n, PairCriterion k s p := by
  let Z := Finset.univ.filter (fun i ↦ k i = 0)
  let N := Finset.univ.filter (fun i ↦ k i ≠ 0)
  have hpartition : Z.card + N.card = n := by
    simpa [Z, N] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i ↦ k i = 0)
  by_cases hfour : 4 ≤ Z.card
  · exact exists_pairCriterion_of_four_zeros hs hker hfour
  by_cases hone : Z.card = 1
  · obtain ⟨z, hzZ⟩ := Finset.card_eq_one.mp hone
    have heq (i : Fin n) : k i = 0 ↔ i = z := by
      have : i ∈ Z ↔ i = z := by rw [hzZ]; simp
      simpa [Z] using this
    exact exists_pairCriterion_of_unique_zero hn hs hker ((heq z).mpr rfl)
      (fun i hi ↦ (heq i).mp hi)
  have htwo : 2 ≤ Z.card := by
    obtain ⟨z, hz⟩ := hz
    have : 0 < Z.card := Finset.card_pos.mpr
      ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    omega
  by_cases hthree : 3 ≤ N.card
  · exact exists_pairCriterion_of_two_zeros_three_nonzeros hs hker htwo hthree
  · exact exists_pairCriterion_of_three_zeros_two_nonzeros hs hker
      (show 3 ≤ Z.card by omega) (show 2 ≤ N.card by omega)

end JanetCartan.CubeCarrier
