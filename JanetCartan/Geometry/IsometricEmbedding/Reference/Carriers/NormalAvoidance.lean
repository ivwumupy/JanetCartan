module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Transversality
import Mathlib.Tactic.FinCases

/-!
# Paired normals avoid the codimension-three bad-normal spaces

The `A,A,B,B,0,…,0` normal from `app:ch_seed:prop:seed-frozen-menu`, Step 1,
has nonzero pairing with a vector in each `L_ijl` and each `L_ijS`.
-/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- The four displayed normal coordinates in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem paired_normal_values {n : ℕ} {w : Euclidean n} {p : Fin 4 ↪ Fin n} {A B : ℝ}
    (hw : ∀ i, w i = (if i = p 0 then A else 0) +
      (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
      (if i = p 3 then B else 0)) :
    ∀ a : Fin 4, w (p a) = ![A,A,B,B] a := by
  intro a
  rw [hw]
  fin_cases a <;> simp [p.injective.eq_iff]

/-- Four nonzero entries cannot be supported on a coordinate triple
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem paired_normal_has_outside_triple {n : ℕ} {w : Euclidean n}
    {p : Fin 4 ↪ Fin n} {A B : ℝ} (hab : A * B * (A - B) ≠ 0)
    (hw : ∀ i, w i = (if i = p 0 then A else 0) +
      (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
      (if i = p 3 then B else 0)) (i j k : Fin n) :
    ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ w l ≠ 0 := by
  have hA : A ≠ 0 := by intro h; simp [h] at hab
  have hB : B ≠ 0 := by intro h; simp [h] at hab
  have hc : ({i,j,k} : Finset (Fin n)).card < (Finset.univ.map p).card := by
    simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have := Finset.card_insert_le i ({j,k} : Finset (Fin n))
    have := Finset.card_insert_le j ({k} : Finset (Fin n))
    simp only [Finset.card_singleton] at *
    omega
  obtain ⟨l, hl, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hl
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  refine ⟨p a, hnot.1, hnot.2.1, hnot.2.2, ?_⟩
  rw [paired_normal_values hw a]
  fin_cases a <;> simp [hA, hB]

private theorem five_values_no_three {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A ≠ B) (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (![A,A,B,B,0] a = ![A,A,B,B,0] b ∧ ![A,A,B,B,0] a = ![A,A,B,B,0] c) := by
  have hBA := Ne.symm hAB
  have h0A := Ne.symm hA
  have h0B := Ne.symm hB
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- The `A,A,B,B` normal has unequal coordinates outside every coordinate
pair, including in dimension five (`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem paired_normal_has_unequal_outside_pair {n : ℕ} (hn : 5 ≤ n)
    {w : Euclidean n} {p : Fin 4 ↪ Fin n} {A B : ℝ} (hab : A * B * (A - B) ≠ 0)
    (hw : ∀ i, w i = (if i = p 0 then A else 0) +
      (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
      (if i = p 3 then B else 0)) (i j : Fin n) :
    ∃ a b : Fin n, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧ w a ≠ w b := by
  have hA : A ≠ 0 := by intro h; simp [h] at hab
  have hB : B ≠ 0 := by intro h; simp [h] at hab
  have hAB : A ≠ B := by intro h; simp [h] at hab
  obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.map p) (t := Finset.univ)
    (by simpa using (show 4 < n by omega))
  have hdp (a : Fin 4) : d ≠ p a := by
    intro h
    exact hd (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, h.symm⟩)
  have hdw : w d = 0 := by simp [hw, hdp]
  let q : Fin 5 ↪ Fin n := {
    toFun := ![p 0, p 1, p 2, p 3, d]
    inj' := by
      intro a b h
      fin_cases a <;> fin_cases b <;>
        simp [p.injective.eq_iff, hdp, Ne.symm (hdp _)] at h ⊢ }
  have hq (a : Fin 5) : w (q a) = ![A,A,B,B,0] a := by
    change w (![p 0, p 1, p 2, p 3, d] a) = _
    fin_cases a <;> simp [paired_normal_values hw, hdw]
  have hno (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      ¬ (w (q a) = w (q b) ∧ w (q a) = w (q c)) := by
    simp only [hq]
    exact five_values_no_three hA hB hAB a b c hab hac hbc
  let T := Finset.univ.map q \ {i,j}
  have hcard : 2 < T.card := by
    have hc := Finset.le_card_sdiff ({i,j} : Finset (Fin n)) (Finset.univ.map q)
    have hb := Finset.card_insert_le i ({j} : Finset (Fin n))
    simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton] at hc hb
    dsimp [T]
    omega
  obtain ⟨a,b,c,ha,hb,hc,hab',hac',hbc'⟩ := Finset.two_lt_card_iff.mp hcard
  have hmem (a : Fin n) (ha : a ∈ T) :
      (∃ t : Fin 5, q t = a) ∧ a ≠ i ∧ a ≠ j := by
    simp only [T, Finset.mem_sdiff, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    exact ⟨ha.1, ha.2⟩
  obtain ⟨⟨a', rfl⟩, hai, haj⟩ := hmem a ha
  obtain ⟨⟨b', rfl⟩, hbi, hbj⟩ := hmem b hb
  obtain ⟨⟨c', rfl⟩, hci, hcj⟩ := hmem c hc
  by_cases heq : w (q a') = w (q b')
  · exact ⟨q a', q c', hai, haj, hci, hcj, fun heq' ↦
      hno a' b' c' (fun h ↦ hab' (congrArg q h))
        (fun h ↦ hac' (congrArg q h)) (fun h ↦ hbc' (congrArg q h)) ⟨heq, heq'⟩⟩
  · exact ⟨q a', q b', hai, haj, hbi, hbj, heq⟩

/-- A witness in each `L_ijl` pairs nontrivially with the normal, proving
avoidance of `L_ijl` perpendicular in `app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem paired_normal_triple_witness {n : ℕ} {w : Euclidean n}
    {p : Fin 4 ↪ Fin n} {A B : ℝ} (hab : A * B * (A - B) ≠ 0)
    (hw : ∀ i, w i = (if i = p 0 then A else 0) +
      (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
      (if i = p 3 then B else 0)) (i j k : Fin n) :
    ∃ x : Euclidean n, x i = 0 ∧ x j = 0 ∧ x k = 0 ∧ (∑ l, x l * w l) ≠ 0 := by
  obtain ⟨l,hli,hlj,hlk,hl⟩ := paired_normal_has_outside_triple hab hw i j k
  refine ⟨EuclideanSpace.single l 1, ?_, ?_, ?_, ?_⟩
  · simp [Ne.symm hli]
  · simp [Ne.symm hlj]
  · simp [Ne.symm hlk]
  · simpa using hl

/-- A witness in each `L_ijS` pairs nontrivially with the normal, proving
avoidance of `L_ijS` perpendicular in `app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem paired_normal_pair_sum_witness {n : ℕ} (hn : 5 ≤ n) {w : Euclidean n}
    {p : Fin 4 ↪ Fin n} {A B : ℝ} (hab : A * B * (A - B) ≠ 0)
    (hw : ∀ i, w i = (if i = p 0 then A else 0) +
      (if i = p 1 then A else 0) + (if i = p 2 then B else 0) +
      (if i = p 3 then B else 0)) (i j : Fin n) :
    ∃ x : Euclidean n, x i = 0 ∧ x j = 0 ∧ (∑ l, x l) = 0 ∧
      (∑ l, x l * w l) ≠ 0 := by
  obtain ⟨a,b,hai,haj,hbi,hbj,hab⟩ := paired_normal_has_unequal_outside_pair hn hab hw i j
  refine ⟨EuclideanSpace.single a 1 - EuclideanSpace.single b 1, ?_, ?_, ?_, ?_⟩
  · simp [Ne.symm hai, Ne.symm hbi]
  · simp [Ne.symm haj, Ne.symm hbj]
  · simp [Finset.sum_sub_distrib]
  · simpa [sub_mul, Finset.sum_sub_distrib] using sub_ne_zero.mpr hab

end JanetCartan.CubeCarrier
