module

public import Mathlib.Data.Nat.Basic

/-!
# Backward finite derivative reserves

The backward choice of finite orders in `app:ch_mean_pairs:prop:mean-coarse`.
`m s` is the initial-data order needed for discrepancy order `s`; `d r` is
the residual order needed to bound the density correction at order `r`.
Neither loss function needs to be monotone or have a fixed additive shift.
-/

@[expose] public section

namespace JanetCartan.BackgroundPreparation

/-- `app:ch_mean_pairs:prop:mean-coarse`: the pair (density order, residual
order) when `k` steps remain, starting with requested final orders `R, S`. -/
def reserves (m d : ℕ → ℕ) (R S : ℕ) : ℕ → ℕ × ℕ
  | 0 => (max R (m S), S)
  | k + 1 =>
    let t := reserves m d R S k
    let s := max t.2 (d t.1)
    (max t.1 (m s), s)

/-- The previous stage reserves enough derivatives for both the next
correction and the next discrepancy (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem reserves_step (m d : ℕ → ℕ) (R S k : ℕ) :
    (reserves m d R S k).1 ≤ (reserves m d R S (k + 1)).1 ∧
    (reserves m d R S k).2 ≤ (reserves m d R S (k + 1)).2 ∧
    d (reserves m d R S k).1 ≤ (reserves m d R S (k + 1)).2 := by
  exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-- Each remaining reserve controls the discrepancy input and the requested
final orders (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem reserves_spec (m d : ℕ → ℕ) (R S k : ℕ) :
    R ≤ (reserves m d R S k).1 ∧ S ≤ (reserves m d R S k).2 ∧
    m (reserves m d R S k).2 ≤ (reserves m d R S k).1 := by
  induction k with
  | zero => exact ⟨Nat.le_max_left _ _, le_rfl, Nat.le_max_right _ _⟩
  | succ k ih =>
    exact ⟨Nat.le_trans ih.1 (reserves_step m d R S k).1,
      Nat.le_trans ih.2.1 (reserves_step m d R S k).2.1, Nat.le_max_right _ _⟩

/-- `app:ch_mean_pairs:prop:mean-coarse`: read the backwards list in forward
iteration order. This is a finite budget for a derivative-losing map. -/
theorem reserves_forward_step (m d : ℕ → ℕ) (R S J i : ℕ) (hi : i < J) :
    (reserves m d R S (J - (i + 1))).1 ≤ (reserves m d R S (J - i)).1 ∧
    d (reserves m d R S (J - (i + 1))).1 ≤ (reserves m d R S (J - i)).2 := by
  have heq : J - i = (J - (i + 1)) + 1 := by omega
  rw [heq]
  exact ⟨(reserves_step m d R S _).1, (reserves_step m d R S _).2.2⟩

end JanetCartan.BackgroundPreparation
