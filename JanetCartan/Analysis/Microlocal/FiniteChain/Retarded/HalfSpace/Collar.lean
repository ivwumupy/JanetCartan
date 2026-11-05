module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Tangential
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Interior

/-!
# Fixed collar partitions and joint amplitude grades

The fixed collar split in `app:ch_regular:lem:finite-chain`, “A common
kernel estimate”. Leibniz bounds give an explicit profile for multiplication
by either member of a fixed smooth partition, preserving the amplitude
offset in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.HalfSpace

/-- `app:ch_regular:lem:finite-chain`: a common Leibniz profile for both
members of a fixed collar partition whose cutoff has derivative profile `H`.
The added one accounts for the zeroth derivative of its complement. -/
def collarAmplitudeProfile (H A : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * (1 + H j) * A (r - j)

/-- `app:ch_regular:lem:finite-chain`: the collar profile is nonnegative. -/
theorem collarAmplitudeProfile_nonneg {H A : ℕ → ℝ}
    (hH : ∀ r, 0 ≤ H r) (hA : ∀ r, 0 ≤ A r) (r : ℕ) :
    0 ≤ collarAmplitudeProfile H A r := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [hH j])) (hA _)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `app:ch_regular:lem:finite-chain`: complementary cutoff derivatives
are bounded by the original fixed profile plus one. -/
theorem norm_iteratedFDeriv_one_sub_le {χ : V → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {x : V} {H : ℕ → ℝ} (hbound : ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ H r)
    (r : ℕ) : ‖iteratedFDeriv ℝ r (1 - χ) x‖ ≤ 1 + H r := by
  change ‖iteratedFDeriv ℝ r ((fun _ : V ↦ (1 : ℂ)) - χ) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply contDiffAt_const (hχ.contDiffAt.of_le (by simp))]
  apply (norm_sub_le _ _).trans
  apply add_le_add _ (hbound r)
  cases r with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ r => simp [iteratedFDeriv_succ_const]

/-- `app:ch_regular:eq:chain-tail`: multiplication by a fixed smooth
cutoff changes only the amplitude profile, not the fixed offset `b`. -/
theorem norm_iteratedFDeriv_collar_mul_le {χ a : V → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a)
    {H A : ℕ → ℝ} (hH : ∀ r, 0 ≤ H r) (hA : ∀ r, 0 ≤ A r)
    {L : ℝ} (hL : 1 ≤ L) (b : ℕ) {x : V}
    (hχ_bound : ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ 1 + H r)
    (ha_bound : ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ A r * L ^ (r + b))
    (r : ℕ) :
    ‖iteratedFDeriv ℝ r (χ * a) x‖ ≤ collarAmplitudeProfile H A r * L ^ (r + b) := by
  apply (norm_iteratedFDeriv_mul_le hχ ha x (show (r : ℕ∞ω) ≤ ∞ by simp)).trans
  rw [collarAmplitudeProfile, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hχj : 0 ≤ 1 + H j := by linarith [hH j]
  calc
    _ ≤ ((r.choose j : ℝ) * (1 + H j)) * (A (r - j) * L ^ (r - j + b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hχ_bound j) (Nat.cast_nonneg _))
        (ha_bound _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hχj)
    _ = ((r.choose j : ℝ) * (1 + H j) * A (r - j)) * L ^ (r - j + b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (Nat.add_le_add_right (Nat.sub_le r j) b))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hχj) (hA _))

end JanetCartan.FiniteChain.Retarded.HalfSpace
