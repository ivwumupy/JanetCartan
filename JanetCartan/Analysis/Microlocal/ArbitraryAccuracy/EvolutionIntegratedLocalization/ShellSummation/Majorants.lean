module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Regimes

/-!
# Majorants for the separated elapsed shell branches

The bounded elapsed interval and the existing physical pair weights give
the scalar summation in `app:ch_regular:eq:chain-tail`. Constants cost at
most four for each branch and eight for their sum. The contracting graph
volumes and output index zero are retained.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable

/-- The noncomparable part of one literal elapsed shell branch. `B` is
the uniform per-time coefficient, before multiplication by the existing
pair weight. The comparable branch is left to the parent's stationary-phase
estimate (`app:ch_regular:eq:chain-tail`). -/
def elapsedSeparatedPairMajorant (d : ℕ) (c C a b ρ Δ B : ℝ)
    (low : Bool) (p : ℕ × ℕ) : ℝ := by
  classical
  exact if IsComparablePair c C a b ρ low p.1 p.2 then 0
    else volume.real (Icc 0 Δ) * B * pairWeight low (d + 1) p.1 p.2

/-- Positivity, summability, and the fixed mass of each separated elapsed
branch. Dimension is `d+1`, so the contracting graph volume is summable
without any lower cutoff (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedSeparatedPairMajorant_properties
    (d : ℕ) (c C a b ρ Δ : ℝ) {B : ℝ} (hB : 0 ≤ B) (low : Bool) :
    (∀ p, 0 ≤ elapsedSeparatedPairMajorant d c C a b ρ Δ B low p) ∧
    Summable (elapsedSeparatedPairMajorant d c C a b ρ Δ B low) ∧
    (∑' p, elapsedSeparatedPairMajorant d c C a b ρ Δ B low p) ≤
      4 * volume.real (Icc 0 Δ) * B := by
  classical
  have hcoef : 0 ≤ volume.real (Icc 0 Δ) * B := mul_nonneg (by positivity) hB
  have hnonneg p : 0 ≤ elapsedSeparatedPairMajorant d c C a b ρ Δ B low p := by
    unfold elapsedSeparatedPairMajorant
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hcoef (pairWeight_nonneg low _ _ _)
  have hle p : elapsedSeparatedPairMajorant d c C a b ρ Δ B low p ≤
      (volume.real (Icc 0 Δ) * B) * pairWeight low (d + 1) p.1 p.2 := by
    unfold elapsedSeparatedPairMajorant
    split_ifs
    · exact mul_nonneg hcoef (pairWeight_nonneg low _ _ _)
    · exact le_rfl
  have hw := (summable_pairWeight (Nat.succ_pos d) low).mul_left (volume.real (Icc 0 Δ) * B)
  have hs := hw.of_nonneg_of_le hnonneg hle
  refine ⟨hnonneg, hs, (hs.tsum_le_tsum hle hw).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (tsum_pairWeight_le_four (Nat.succ_pos d) low)
    hcoef).trans_eq (by ring)

/-- The sum of the two separated majorants is summable with a common
fixed mass. This is the majorant used after exact high/low reassembly;
it preserves both independent indices (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedSeparatedPairMajorant_both_branches
    (d : ℕ) (c C a b ρ Δ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    Summable (fun p ↦ elapsedSeparatedPairMajorant d c C a b ρ Δ B false p +
      elapsedSeparatedPairMajorant d c C a b ρ Δ B true p) ∧
    (∑' p, (elapsedSeparatedPairMajorant d c C a b ρ Δ B false p +
      elapsedSeparatedPairMajorant d c C a b ρ Δ B true p)) ≤
        8 * volume.real (Icc 0 Δ) * B := by
  have hh := elapsedSeparatedPairMajorant_properties d c C a b ρ Δ hB false
  have hl := elapsedSeparatedPairMajorant_properties d c C a b ρ Δ hB true
  refine ⟨hh.2.1.add hl.2.1, ?_⟩
  rw [hh.2.1.tsum_add hl.2.1]
  exact (add_le_add hh.2.2 hl.2.2).trans_eq (by ring)

/-- The separated branch mass has the requested accuracy form, with the
fixed physical frequency loss `C_A = d+1` and the unchanged fixed `L`
offset. Only `D N` varies with accuracy. The per-time producer chooses
`bLoss = bi + (m + bo) + bA + threshold + 2` before `N`; no relation
`L ≤ ρ` is needed for this deduction (`app:ch_regular:eq:chain-tail`). -/
theorem elapsedSeparatedPairMajorant_accuracy_bound
    (d m bLoss N : ℕ) (c C a b Δ : ℝ) {ρ L D : ℝ}
    (hρ : 1 ≤ ρ) (hL : 0 ≤ L) (hD : 0 ≤ D) (low : Bool) :
    (∑' p, elapsedSeparatedPairMajorant d c C a b ρ Δ
      (D * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N) low p) ≤
      (4 * volume.real (Icc 0 Δ) * D) * ρ ^ (m + (d + 1)) *
        L ^ bLoss * (L / ρ) ^ N := by
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hB : 0 ≤ D * ρ ^ (d + 1) * L ^ bLoss * (L / ρ) ^ N := by positivity
  apply (elapsedSeparatedPairMajorant_properties d c C a b ρ Δ hB low).2.2.trans
  have hp : ρ ^ (d + 1) ≤ ρ ^ (m + (d + 1)) :=
    pow_le_pow_right₀ hρ (by omega)
  have hcoef : 0 ≤ 4 * volume.real (Icc 0 Δ) * D * L ^ bLoss * (L / ρ) ^ N := by positivity
  convert mul_le_mul_of_nonneg_left hp hcoef using 1 <;> ring

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
