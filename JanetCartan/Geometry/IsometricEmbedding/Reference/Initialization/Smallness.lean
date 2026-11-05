module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One scale for finitely many thresholds

The final parameter choice after `main:prop:seed`: finitely many positive
accuracy thresholds can be met by one positive scale below a prescribed cap.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- `main:eq:seed-small`: choose a single positive dilation below an existing
domain cap and below finitely many linear error thresholds. -/
theorem exists_scale_for_finite_thresholds {ι : Type*} (S : Finset ι)
    (C ε : ι → ℝ) (hC : ∀ i, 0 < C i) (hε : ∀ i ∈ S, 0 < ε i)
    {sMax : ℝ} (hsMax : 0 < sMax) :
    ∃ s : ℝ, 0 < s ∧ s ≤ sMax ∧ ∀ i ∈ S, C i * s < ε i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨sMax, hsMax, le_rfl, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨t, ht, htMax, htε⟩ := ih (fun j hj ↦ hε j (Finset.mem_insert_of_mem hj))
    have hεi := hε i (Finset.mem_insert_self i S)
    have hCi := hC i
    let s := min t (ε i / (2 * C i))
    have hs : 0 < s := lt_min ht (by positivity)
    have hst : s ≤ t := min_le_left _ _
    refine ⟨s, hs, hst.trans htMax, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hj
    · rw [hji]
      have hsmall : s * (2 * C i) ≤ ε i :=
        (le_div_iff₀ (by positivity)).mp (min_le_right t _)
      nlinarith
    · exact (mul_le_mul_of_nonneg_left hst (hC j).le).trans_lt (htε j hj)

end JanetCartan
