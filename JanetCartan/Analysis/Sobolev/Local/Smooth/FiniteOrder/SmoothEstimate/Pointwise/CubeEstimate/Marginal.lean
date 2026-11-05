module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite coordinate averaging on a unit cube

The measure-theoretic induction below iterates coordinate averaging for the
Sobolev norms of `app:not:fourier`, as used in
`app:ch_regular:thm:exact-correction`. Marginal integrals implement Tonelli's
theorem without any integrability or finiteness assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- Iterating coordinate bounds gives the unit-cube averaging estimate used in
`app:ch_regular:thm:exact-correction`, with derivative orders as in
`app:not:fourier`. The functions may take the value `∞`, and the statement
includes dimension zero. -/
theorem le_two_pow_mul_sum_lintegral_Icc_of_coordinate_bounds
    (n : ℕ) (a : Fin n → ℝ) (G : ℕ → (Fin n → ℝ) → ℝ≥0∞)
    (hmeas : ∀ l, Measurable (G l))
    (hstep : ∀ (l : ℕ) (i : Fin n) (z : Fin n → ℝ), z i = a i →
      G l z ≤ (∫⁻ t in Icc (a i) (a i + 1), G l (Function.update z i t)) +
        ∫⁻ t in Icc (a i) (a i + 1), G (l + 1) (Function.update z i t)) :
    G 0 a ≤ (2 : ℝ≥0∞) ^ n *
      ∑ l ∈ Finset.range (n + 1), ∫⁻ z in Icc a (fun i ↦ a i + 1), G l z := by
  let μ : Fin n → Measure ℝ := fun i ↦ volume.restrict (Icc (a i) (a i + 1))
  have hbound (s : Finset (Fin n)) (k : ℕ) (z : Fin n → ℝ)
      (hz : ∀ i ∈ s, z i = a i) :
      G k z ≤ (2 : ℝ≥0∞) ^ s.card *
        ∑ l ∈ Finset.range (s.card + 1), lmarginal μ s (G (k + l)) z := by
    induction s using Finset.induction generalizing k z with
    | empty => simp
    | @insert i s hi ih =>
      have hz' (t : ℝ) : ∀ j ∈ s, Function.update z i t j = a j := by
        intro j hj
        rw [Function.update_of_ne (by intro h; subst j; exact hi hj)]
        exact hz j (Finset.mem_insert_of_mem hj)
      have hint (r : ℕ) :
          (∫⁻ t, G r (Function.update z i t) ∂μ i) ≤
            (2 : ℝ≥0∞) ^ s.card *
              ∑ l ∈ Finset.range (s.card + 1), lmarginal μ (insert i s) (G (r + l)) z := by
        calc
          _ ≤ ∫⁻ t, (2 : ℝ≥0∞) ^ s.card *
              ∑ l ∈ Finset.range (s.card + 1),
                lmarginal μ s (G (r + l)) (Function.update z i t) ∂μ i :=
            lintegral_mono (fun t ↦ ih r _ (hz' t))
          _ = _ := by
            rw [lintegral_const_mul' _ _ (by simp)]
            rw [lintegral_finsetSum (f := fun l t ↦
              lmarginal μ s (G (r + l)) (Function.update z i t)) _ (fun l _ ↦
              ((hmeas (r + l)).lmarginal (s := s) μ).comp (measurable_update (a := i) z))]
            simp_rw [← lmarginal_insert _ (hmeas _) hi]
      have hfirst :
          (∑ l ∈ Finset.range (s.card + 1), lmarginal μ (insert i s) (G (k + l)) z) ≤
          ∑ l ∈ Finset.range (s.card + 1 + 1), lmarginal μ (insert i s) (G (k + l)) z :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ _))
      have hsecond :
          (∑ l ∈ Finset.range (s.card + 1),
            lmarginal μ (insert i s) (G (k + 1 + l)) z) ≤
          ∑ l ∈ Finset.range (s.card + 1 + 1), lmarginal μ (insert i s) (G (k + l)) z := by
        rw [Finset.sum_range_succ' _ (s.card + 1)]
        simp only [Nat.add_assoc, Nat.add_comm 1]
        exact le_add_right le_rfl
      calc
        G k z ≤ (∫⁻ t, G k (Function.update z i t) ∂μ i) +
            ∫⁻ t, G (k + 1) (Function.update z i t) ∂μ i :=
          hstep k i z (hz i (Finset.mem_insert_self i s))
        _ ≤ (2 : ℝ≥0∞) ^ s.card *
              (∑ l ∈ Finset.range (s.card + 1 + 1),
                lmarginal μ (insert i s) (G (k + l)) z) +
            (2 : ℝ≥0∞) ^ s.card *
              (∑ l ∈ Finset.range (s.card + 1 + 1),
                lmarginal μ (insert i s) (G (k + l)) z) :=
          add_le_add ((hint k).trans (mul_le_mul' le_rfl hfirst))
            ((hint (k + 1)).trans (mul_le_mul' le_rfl hsecond))
        _ = _ := by
          rw [Finset.card_insert_of_notMem hi, ← two_mul, pow_succ]
          ring
  have h := hbound Finset.univ 0 a (fun _ _ ↦ rfl)
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.zero_add, lmarginal_univ, μ,
    ← Measure.restrict_pi_pi, pi_univ_Icc, ← volume_pi] using h

end JanetCartan.LocalSobolev.FiniteOrder
