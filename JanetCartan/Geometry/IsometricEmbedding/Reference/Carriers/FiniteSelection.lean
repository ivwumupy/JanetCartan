module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Selection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Finite pair-selection tools for `app:ch_seed:prop:seed-frozen-menu` -/

@[expose] public noncomputable section
namespace JanetCartan.CubeCarrier

/-- Four distinct indices define the ordered pairs used in
`app:ch_seed:eq:seed-pair-criterion`. -/
def embeddingFour {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ Fin n where
  toFun := ![a,b,c,d]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- On at least three indices a nonzero vector has a nonzero pair sum
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_pair_sum_ne_zero {n : ℕ} (s : Euclidean n)
    (Z : Finset (Fin n)) (hZ : 3 ≤ Z.card) (hs : ∃ i ∈ Z, s i ≠ 0) :
    ∃ a ∈ Z, ∃ b ∈ Z, a ≠ b ∧ s a + s b ≠ 0 := by
  obtain ⟨a, ha, hsa⟩ := hs
  have hcard : 2 ≤ (Z.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  let p := (Z.erase a).orderEmbOfCardLe hcard
  let b := p 0
  let c := p 1
  have hb := Finset.mem_erase.mp ((Z.erase a).orderEmbOfCardLe_mem hcard 0)
  have hc := Finset.mem_erase.mp ((Z.erase a).orderEmbOfCardLe_mem hcard 1)
  have hbc : b ≠ c := fun h ↦ (by norm_num : (0 : Fin 2) ≠ 1) (p.injective h)
  by_cases hab : s a + s b ≠ 0
  · exact ⟨a, ha, b, hb.2, Ne.symm hb.1, hab⟩
  by_cases hac : s a + s c ≠ 0
  · exact ⟨a, ha, c, hc.2, Ne.symm hc.1, hac⟩
  exact ⟨b, hb.2, c, hc.2, hbc, by push Not at hab hac; intro h; apply hsa; linarith⟩


end JanetCartan.CubeCarrier
