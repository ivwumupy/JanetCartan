module

public import JanetCartan.Analysis.Iteration.BackgroundPreparation.Algebra
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite density estimates with decreasing reserves

The finite induction in `app:ch_mean_pairs:prop:mean-coarse`. The seminorms
`p i` and `q i` may lose derivatives at each step. Lipschitz estimates are
needed only on a bounded positive class; membership of every iterate is
proved by the induction, not assumed. No infinite iteration is used.
-/

@[expose] public noncomputable section

namespace JanetCartan.BackgroundPreparation

open Finset

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- `app:ch_mean_pairs:prop:mean-coarse`: a finite geometric sum bounds the
cumulative correction at a large carrier threshold. -/
theorem finite_geometric_sum_le_two {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2)
    (i : ℕ) : ∑ k ∈ range i, t ^ k ≤ 2 := by
  calc
    _ ≤ ∑ k ∈ range i, (1 / 2 : ℝ) ^ k :=
      sum_le_sum (fun k _ ↦ pow_le_pow_left₀ ht ht' k)
    _ ≤ 2 := sum_geometric_two_le i

/-- The finite preparation induction of `app:ch_mean_pairs:prop:mean-coarse`.
`ε = λ⁻¹`; `C` bounds the initial discrepancy, `M` the density correction,
and `K` its discrepancy Lipschitz constant. The input seminorm at step `i`
can be stronger than the output seminorm at step `i+1`. The two smallness
conditions ensure the local estimates can be applied at every step. -/
theorem finite_preparation_bounds
    (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Y) (E : X → Y)
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (J : ℕ)
    {ε C M K ρ : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hsmall : K * M * ε ≤ 1 / 2) (hradius : 2 * M * C * ε ≤ ρ)
    (hcancel : ∀ e, L (D e) - B e = -e)
    (hmono : ∀ i < J, ∀ v, p (i + 1) v ≤ p i v)
    (hD : ∀ i < J, ∀ e, p (i + 1) (D e) ≤ M * q i e)
    (hE : ∀ i < J, ∀ v w, p (i + 1) v ≤ ρ → p (i + 1) w ≤ ρ →
      q (i + 1) (E v - E w) ≤ K * ε * p (i + 1) (v - w))
    (hinit : q 0 (E 0) ≤ C * ε) :
    ∀ i ≤ J,
      q i (run D L B E i).2 ≤ C * ε * (K * M * ε) ^ i ∧
      p i (run D L B E i).1 ≤
        M * C * ε * ∑ k ∈ range i, (K * M * ε) ^ k ∧
      p i (run D L B E i).1 ≤ 2 * M * C * ε := by
  have ht : 0 ≤ K * M * ε := by positivity
  have hcoef : 0 ≤ M * C * ε := by positivity
  intro i
  induction i with
  | zero =>
    intro _
    simpa [run] using And.intro hinit (show (0 : ℝ) ≤ 0 ∧ 0 ≤ 2 * M * C * ε by
      constructor <;> positivity)
  | succ i ih =>
    intro hi
    have hiJ : i < J := by omega
    obtain ⟨he, hv, _⟩ := ih (by omega)
    have hd : p (i + 1) (D (run D L B E i).2) ≤
        M * (C * ε * (K * M * ε) ^ i) :=
      (hD i hiJ _).trans (mul_le_mul_of_nonneg_left he hM)
    have hvnext : p (i + 1) (run D L B E (i + 1)).1 ≤
        M * C * ε * ∑ k ∈ range (i + 1), (K * M * ε) ^ k := by
      change p (i + 1) ((run D L B E i).1 + D (run D L B E i).2) ≤ _
      calc
        _ ≤ p (i + 1) (run D L B E i).1 + p (i + 1) (D (run D L B E i).2) :=
          map_add_le_add _ _ _
        _ ≤ M * C * ε * ∑ k ∈ range i, (K * M * ε) ^ k +
            M * (C * ε * (K * M * ε) ^ i) :=
          add_le_add ((hmono i hiJ _).trans hv) hd
        _ = _ := by rw [sum_range_succ]; ring
    have hvbound : p (i + 1) (run D L B E (i + 1)).1 ≤ 2 * M * C * ε :=
      hvnext.trans (by
        calc
          _ ≤ M * C * ε * 2 := mul_le_mul_of_nonneg_left
            (finite_geometric_sum_le_two ht hsmall (i + 1)) hcoef
          _ = _ := by ring)
    refine ⟨?_, hvnext, hvbound⟩
    have hvold : p (i + 1) (run D L B E i).1 ≤ ρ := by
      apply (hmono i hiJ _).trans
      apply hv.trans
      exact (show M * C * ε * ∑ k ∈ range i, (K * M * ε) ^ k ≤
          2 * M * C * ε from (by
        nlinarith [mul_le_mul_of_nonneg_left
          (finite_geometric_sum_le_two ht hsmall i) hcoef])).trans hradius
    rw [run_residual_succ D L B E hcancel]
    calc
      _ ≤ K * ε * p (i + 1)
          ((run D L B E (i + 1)).1 - (run D L B E i).1) :=
        hE i hiJ _ _ (hvbound.trans hradius) hvold
      _ = K * ε * p (i + 1) (D (run D L B E i).2) := by
        congr 2
        change (run D L B E i).1 + D (run D L B E i).2 - (run D L B E i).1 = _
        abel
      _ ≤ K * ε * (M * (C * ε * (K * M * ε) ^ i)) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hK hε)
      _ = C * ε * (K * M * ε) ^ (i + 1) := by rw [pow_succ]; ring

/-- `app:ch_mean_pairs:prop:mean-coarse`: the geometric bound is precisely
order `λ^(-(i+1))`, with a finite constant depending on the number of updates. -/
theorem preparation_power_identity (C K M Λ : ℝ) (i : ℕ) :
    C * Λ⁻¹ * (K * M * Λ⁻¹) ^ i = C * (K * M) ^ i * (Λ⁻¹) ^ (i + 1) := by
  rw [mul_pow, pow_succ]
  ring

/-- `app:ch_mean_pairs:prop:mean-coarse`: any auxiliary correction with the
stated finite-order bound accumulates to `O(ε)`. Apply this to the auxiliary
field update and use `finite_preparation_bounds` for `he`. -/
theorem auxiliary_correction_sum_le {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (t : Seminorm ℝ Z) (A : ℕ → Y →ₗ[ℝ] Z) (q : ℕ → Seminorm ℝ Y)
    (e : ℕ → Y) (J : ℕ) {ε C M K N : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hsmall : K * M * ε ≤ 1 / 2)
    (he : ∀ i < J, q i (e i) ≤ C * ε * (K * M * ε) ^ i)
    (hA : ∀ i < J, ∀ y, t (A i y) ≤ N * q i y) :
    t (∑ i ∈ range J, A i (e i)) ≤ 2 * N * C * ε := by
  have hsum : t (∑ i ∈ range J, A i (e i)) ≤
      ∑ i ∈ range J, t (A i (e i)) := by
    have haux (j : ℕ) : t (∑ i ∈ range j, A i (e i)) ≤
        ∑ i ∈ range j, t (A i (e i)) := by
      induction j with
      | zero => simp
      | succ j ih =>
        simp only [sum_range_succ]
        exact (map_add_le_add t _ _).trans (add_le_add ih le_rfl)
    exact haux J
  calc
    _ ≤ ∑ i ∈ range J, t (A i (e i)) := hsum
    _ ≤ ∑ i ∈ range J, N * (C * ε * (K * M * ε) ^ i) := by
      apply sum_le_sum
      intro i hi
      exact (hA i (mem_range.mp hi) _).trans
        (mul_le_mul_of_nonneg_left (he i (mem_range.mp hi)) hN)
    _ = (N * C * ε) * ∑ i ∈ range J, (K * M * ε) ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (N * C * ε) * 2 := mul_le_mul_of_nonneg_left
      (finite_geometric_sum_le_two (by positivity) hsmall J) (by positivity)
    _ = _ := by ring

end JanetCartan.BackgroundPreparation
