module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Regimes

/-!
# Summable weights for the exhaustive physical pair regimes

The finite comparable remainder and the noncomparable geometric weights are
combined without deleting the low graph tail or the bounded output ball.
The constants precede the input scale (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open Noncomparable

/-- Weight for one actual graph branch, with value one on the comparable
remainder and the proved geometric weight elsewhere
(`app:ch_regular:eq:chain-tail`). -/
def regimePairWeight (n : ℕ) (c C a b ρ : ℝ) (low : Bool) (p : ℕ × ℕ) : ℝ := by
  classical
  exact if IsComparablePair c C a b ρ low p.1 p.2 then 1 else pairWeight low n p.1 p.2

/-- Both parts of the exhaustive pair majorant are nonnegative
(`app:ch_regular:eq:chain-tail`). -/
theorem regimePairWeight_nonneg (n : ℕ) (c C a b ρ : ℝ) (low : Bool) (p : ℕ × ℕ) :
    0 ≤ regimePairWeight n c C a b ρ low p := by
  classical
  unfold regimePairWeight
  split_ifs
  · norm_num
  · exact pairWeight_nonneg low n p.1 p.2

/-- The mass of either branch is uniformly bounded before the input scale
is chosen. No relation between the two shell indices is imposed. Dimension
zero is handled by `Noncomparable.physicalPair_dim_zero`, rather than by a
false summability assertion about zero-dimensional volumes
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_regimePairWeight_mass {n : ℕ} (hn : 0 < n)
    (c C b : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ low : Bool,
      Summable (regimePairWeight n c C a b ρ low) ∧
        (∑' p, regimePairWeight n c C a b ρ low p) ≤ M := by
  classical
  obtain ⟨N, hN⟩ := exists_finite_comparablePairs c C b ha
  refine ⟨(N : ℝ) + 4, by positivity, ?_⟩
  intro ρ hρ low
  obtain ⟨s, hs, hmem⟩ := hN ρ hρ low
  let f : ℕ × ℕ → ℝ := fun p => if p ∈ s then 1 else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := s) (by
    intro p hp
    simp [f, hp])
  have hsum : (∑' p, f p) = s.card := by
    rw [tsum_eq_sum (s := s) (by intro p hp; simp [f, hp])]
    simp [f]
  have hw := summable_pairWeight hn low
  have hle p : regimePairWeight n c C a b ρ low p ≤ f p + pairWeight low n p.1 p.2 := by
    by_cases hp : p ∈ s
    · have hc := (hmem p.1 p.2).mp hp
      simp only [regimePairWeight, hc, ↓reduceIte, f, hp]
      linarith [pairWeight_nonneg low n p.1 p.2]
    · have hc : ¬ IsComparablePair c C a b ρ low p.1 p.2 :=
        fun h => hp ((hmem p.1 p.2).mpr h)
      simp [regimePairWeight, hc, f, hp]
  have hreg := (hf.add hw).of_nonneg_of_le (regimePairWeight_nonneg n c C a b ρ low) hle
  refine ⟨hreg, ?_⟩
  calc
    _ ≤ ∑' p, (f p + pairWeight low n p.1 p.2) := hreg.tsum_le_tsum hle (hf.add hw)
    _ = (s.card : ℝ) + ∑' p : ℕ × ℕ, pairWeight low n p.1 p.2 := by
      rw [hf.tsum_add hw, hsum]
    _ ≤ (N : ℝ) + 4 := add_le_add (by exact_mod_cast hs) (tsum_pairWeight_le_four hn low)

/-- Weight for the original `graphCutoff`, the sum of its exact high and
low physical pieces (`app:ch_regular:eq:joint-kernel-phase`). -/
def graphPairWeight (n : ℕ) (c C a b ρ : ℝ) (p : ℕ × ℕ) : ℝ :=
  regimePairWeight n c C a b ρ false p + regimePairWeight n c C a b ρ true p

/-- The physical graph-cutoff majorant is nonnegative
(`app:ch_regular:eq:chain-tail`). -/
theorem graphPairWeight_nonneg (n : ℕ) (c C a b ρ : ℝ) (p : ℕ × ℕ) :
    0 ≤ graphPairWeight n c C a b ρ p :=
  add_nonneg (regimePairWeight_nonneg ..) (regimePairWeight_nonneg ..)

/-- The high and low branches together have uniformly bounded summable
mass. Multiplication by the physical pair constants therefore introduces
no additional frequency or accuracy loss (`app:ch_regular:eq:chain-tail`). -/
theorem exists_graphPairWeight_mass {n : ℕ} (hn : 0 < n)
    (c C b : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      Summable (graphPairWeight n c C a b ρ) ∧
        (∑' p, graphPairWeight n c C a b ρ p) ≤ M := by
  obtain ⟨M, hM, hm⟩ := exists_regimePairWeight_mass hn c C b ha
  refine ⟨M + M, add_nonneg hM hM, ?_⟩
  intro ρ hρ
  have hh := hm ρ hρ false
  have hl := hm ρ hρ true
  refine ⟨hh.1.add hl.1, ?_⟩
  change (∑' p : ℕ × ℕ, (regimePairWeight n c C a b ρ false p + regimePairWeight n c C a b ρ true p)) ≤ _
  rw [hh.1.tsum_add hl.1]
  exact add_le_add hh.2 hl.2

end JanetCartan.FiniteChain.Graph.PhysicalShells
