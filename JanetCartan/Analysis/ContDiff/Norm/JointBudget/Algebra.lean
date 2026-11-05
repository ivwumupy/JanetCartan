module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebra for joint derivative budgets

The algebraic part of `app:ch_regular_base:eq:joint-primitive-product` and
`app:cor:fixed-profile-transfer`. Natural subtraction records the positive part
of each derivative excess. Interpolation is an explicit input, not asserted here.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.JointBudget

/-- `app:ch_regular_base:eq:joint-primitive-product`: one factor, including the
low and high endpoints, from the precise intermediate-order interpolation bound.
`K` is a uniform upper bound for the finitely many interpolation constants. -/
theorem interpolation_le_scaled_rpow
    (a : ℕ → ℝ) (b W j : ℕ) (B K H : ℝ)
    (ha : ∀ r, 0 ≤ a r) (hmono : Monotone a)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : a b ≤ B) (hhigh : a (b + W) ≤ H) (hj : j ≤ b + W)
    (hinterp : b < j → j < b + W →
      a j ≤ K * a b ^ (1 - ((j - b : ℕ) : ℝ) / W) *
        a (b + W) ^ (((j - b : ℕ) : ℝ) / W)) :
    a j ≤ (K * B) * H ^ (((j - b : ℕ) : ℝ) / W) := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hKB : B ≤ K * B := by nlinarith
  by_cases hjb : j ≤ b
  · simpa [Nat.sub_eq_zero_of_le hjb] using (hmono hjb).trans (hlow.trans hKB)
  have hbj : b < j := by omega
  have hW : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have ht0 : 0 ≤ ((j - b : ℕ) : ℝ) / W := by positivity
  have ht1 : ((j - b : ℕ) : ℝ) / W ≤ 1 := by
    apply (div_le_one hWr).2
    exact_mod_cast (show j - b ≤ W by omega)
  by_cases htop : j = b + W
  · have ht : ((j - b : ℕ) : ℝ) / W = 1 := by
      simp [htop, ne_of_gt hWr]
    rw [ht, Real.rpow_one]
    calc
      a j ≤ H := htop ▸ hhigh
      _ ≤ (K * B) * H := by nlinarith
  have hlowpow : a b ^ (1 - ((j - b : ℕ) : ℝ) / W) ≤ B :=
    (Real.rpow_le_rpow (ha b) hlow (sub_nonneg.mpr ht1)).trans
      (Real.rpow_le_self_of_one_le hB (by linarith))
  have hhighpow := Real.rpow_le_rpow (ha (b + W)) hhigh ht0
  exact (hinterp hbj (by omega)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hlowpow hK0) hhighpow
      (Real.rpow_nonneg (ha (b + W)) _) (mul_nonneg hK0 hB0))

/-- `app:ch_regular_base:eq:joint-primitive-product`: a finite product with
repeated primitive indices and a joint truncated derivative budget. The constant
`(K * B) ^ s.card` depends only on low bounds, interpolation, and factor count.
This is conditional on the displayed interpolation estimate. -/
theorem finite_product_le_one_high
    {ι α : Type*} (I : Finset ι) (s : Finset α)
    (a : ι → ℕ → ℝ) (b : ι → ℕ) (index : α → ι) (j : α → ℕ)
    (W : ℕ) (B K : ℝ)
    (ha : ∀ i ∈ I, ∀ r, 0 ≤ a i r)
    (hmono : ∀ i ∈ I, Monotone (a i))
    (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hlow : ∀ i ∈ I, a i (b i) ≤ B)
    (hindex : ∀ h ∈ s, index h ∈ I)
    (hbudget : ∑ h ∈ s, (j h - b (index h)) ≤ W)
    (hinterp : ∀ i ∈ I, ∀ q, b i < q → q < b i + W →
      a i q ≤ K * a i (b i) ^ (1 - ((q - b i : ℕ) : ℝ) / W) *
        a i (b i + W) ^ (((q - b i : ℕ) : ℝ) / W)) :
    ∏ h ∈ s, a (index h) (j h) ≤
      (K * B) ^ s.card * (1 + ∑ i ∈ I, a i (b i + W)) := by
  let H := 1 + ∑ i ∈ I, a i (b i + W)
  have hsum : 0 ≤ ∑ i ∈ I, a i (b i + W) :=
    Finset.sum_nonneg fun i hi ↦ ha i hi _
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hKB : 0 ≤ K * B := mul_nonneg (by linarith) (by linarith)
  have hfactor (h : α) (hh : h ∈ s) :
      a (index h) (j h) ≤
        (K * B) * H ^ (((j h - b (index h) : ℕ) : ℝ) / W) := by
    have hi := hindex h hh
    have hexcess : j h - b (index h) ≤ W :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hh).trans hbudget
    apply interpolation_le_scaled_rpow (a (index h)) (b (index h)) W (j h) B K H
      (ha _ hi) (hmono _ hi) hB hK hH (hlow _ hi) ?_ (by omega)
      (hinterp _ hi (j h))
    have := Finset.single_le_sum (fun i hi ↦ ha i hi (b i + W)) hi
    dsimp [H]
    linarith
  have htheta : (∑ h ∈ s, (((j h - b (index h) : ℕ) : ℝ) / W)) ≤ 1 := by
    rw [← Finset.sum_div]
    by_cases hW : W = 0
    · simp [hW]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hW)).2
      exact_mod_cast hbudget
  calc
    ∏ h ∈ s, a (index h) (j h) ≤
        ∏ h ∈ s, ((K * B) * H ^ (((j h - b (index h) : ℕ) : ℝ) / W)) :=
      Finset.prod_le_prod₀ (fun h hh ↦ ha _ (hindex h hh) _) hfactor
    _ = (K * B) ^ s.card * H ^ (∑ h ∈ s, (((j h - b (index h) : ℕ) : ℝ) / W)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos (by linarith)]
    _ ≤ (K * B) ^ s.card * H :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hH htheta) (pow_nonneg hKB _)

/-- `app:cor:fixed-profile-transfer`: finite derivative loss preserves the
truncated profile when `c + ν ≤ R`, with the explicit new constant `C * (1 + A)`. -/
theorem fixed_profile_transfer_bound
    {T A C x y : ℝ} {r c R ν : ℕ}
    (hT : 1 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hloss : c + ν ≤ R)
    (hx : x ≤ A * T ^ (r + c - R)) (hy : y ≤ C * (1 + x)) :
    y ≤ (C * (1 + A)) * T ^ (r - ν) := by
  have hexponent : r + c - R ≤ r - ν := by omega
  have hp := pow_le_pow_right₀ hT hexponent
  have hone : 1 ≤ T ^ (r - ν) := one_le_pow₀ hT
  calc
    y ≤ C * (1 + x) := hy
    _ ≤ C * (1 + A * T ^ (r + c - R)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hx) hC
    _ ≤ C * (1 + A * T ^ (r - ν)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hA)) hC
    _ ≤ C * (T ^ (r - ν) + A * T ^ (r - ν)) :=
      mul_le_mul_of_nonneg_left (add_le_add hone le_rfl) hC
    _ = (C * (1 + A)) * T ^ (r - ν) := by ring

end JanetCartan.JointBudget
