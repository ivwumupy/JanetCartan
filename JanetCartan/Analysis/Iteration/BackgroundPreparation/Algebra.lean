module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# The uncut density preparation ledger

The finite recurrence of `app:ch_mean_pairs:eq:mean-density-recursion`.
`D` is the signed density correction, `L` the measured transported density,
and `B` the auxiliary normal followed by the fixed inverse. All are actual
linear maps. Their cancellation identity is an explicit input.
-/

@[expose] public noncomputable section

namespace JanetCartan.BackgroundPreparation

open Finset

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- `app:ch_mean_pairs:eq:mean-density-recursion`: update the density and the
full residual, retaining both linear corrections before cancellation. -/
def run (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Y)
    (E : X → Y) : ℕ → X × Y
  | 0 => (0, E 0)
  | i + 1 =>
    let z := run D L B E i
    (z.1 + D z.2, z.2 + L (D z.2) - B z.2 + (E (z.1 + D z.2) - E z.1))

/-- `app:ch_mean_pairs:eq:mean-density-recursion`: the density is the finite
sum of the actual signed corrections. -/
theorem run_density_eq_sum (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y)
    (B : Y →ₗ[ℝ] Y) (E : X → Y) (i : ℕ) :
    (run D L B E i).1 = ∑ k ∈ range i, D (run D L B E k).2 := by
  induction i with
  | zero => simp [run]
  | succ i ih =>
    simpa only [run, sum_range_succ] using
      congrArg (fun v ↦ v + D (run D L B E i).2) ih

/-- The full residual definition preceding
`app:ch_mean_pairs:eq:mean-density-recursion`, including the auxiliary component. -/
theorem run_residual_ledger (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y)
    (B : Y →ₗ[ℝ] Y) (E : X → Y) (i : ℕ) :
    (run D L B E i).2 = E (run D L B E i).1 + L (run D L B E i).1 -
      ∑ k ∈ range i, B (run D L B E k).2 := by
  induction i with
  | zero => simp [run]
  | succ i ih =>
    change (run D L B E i).2 + L (D (run D L B E i).2) -
      B (run D L B E i).2 +
      (E ((run D L B E i).1 + D (run D L B E i).2) - E (run D L B E i).1) = _
    conv_lhs => enter [1, 1, 1]; rw [ih]
    simp only [run, map_add, sum_range_succ]
    abel

/-- `app:ch_mean_pairs:eq:mean-density-recursion`: exact cancellation by the
uncut right inverse leaves only the Hermitian discrepancy difference. -/
theorem run_residual_succ (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y)
    (B : Y →ₗ[ℝ] Y) (E : X → Y)
    (hcancel : ∀ e, L (D e) - B e = -e) (i : ℕ) :
    (run D L B E (i + 1)).2 =
      E (run D L B E (i + 1)).1 - E (run D L B E i).1 := by
  change (run D L B E i).2 + L (D (run D L B E i).2) -
    B (run D L B E i).2 + _ = _
  rw [add_sub_assoc, hcancel, add_neg_cancel, zero_add]
  rfl

/-- `app:ch_mean_pairs:eq:mean-density-recursion`: the row right-inverse
identity and the signed density synthesis imply the required cancellation.
`T` and `A` represent the two normal blocks and `Q` is the original inverse. -/
theorem cancellation_of_normal_inverse (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y)
    (T A Q : Y →ₗ[ℝ] Y)
    (hdensity : ∀ e, L (D e) = -T (Q e))
    (hinverse : ∀ e, T (Q e) + A (Q e) = e) :
    ∀ e, L (D e) - (A.comp Q) e = -e := by
  intro e
  rw [hdensity, LinearMap.comp_apply, sub_eq_add_neg, ← neg_add]
  exact congrArg Neg.neg (hinverse e)

end JanetCartan.BackgroundPreparation
