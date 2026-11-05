module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Frequency
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget.Algebra

/-!
# One-high budgets for the explicit transport products

The Leibniz convolution retains the interpolation exponent at every intermediate
order. This is essential in `app:ch_regular_base:eq:actual-one-high`: nested
products must share a single high coefficient norm. The inputs here are precise
primitive interpolation profiles, with a fixed jet shift `δ`. Establishing those
profiles from the buffered primitive bounds remains a separate analytic step.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace JanetCartan.FourierIntegral

/-- Nonnegativity of the uncollapsed product budget in
`app:ch_regular_base:eq:joint-primitive-product`. -/
theorem transportLeibnizBound_nonneg {p q : ℕ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) (n : ℕ) :
    0 ≤ transportLeibnizBound p q n :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hp i)) (hq (n - i))

/-- Exact interpolation-exponent bookkeeping for a noncommutative product's
scalar norm bound (`app:ch_regular_base:eq:joint-primitive-product`). The fixed
primitive shifts add; the variable derivative count occurs only once. -/
theorem transportLeibnizBound_rpow (P Q : ℕ → ℝ) {H : ℝ} (hH : 0 < H)
    (W a b n : ℕ) :
    transportLeibnizBound (fun k ↦ P k * H ^ (((k + a : ℕ) : ℝ) / W))
      (fun k ↦ Q k * H ^ (((k + b : ℕ) : ℝ) / W)) n =
      transportLeibnizBound P Q n * H ^ (((n + (a + b) : ℕ) : ℝ) / W) := by
  unfold transportLeibnizBound
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hexp : (((i + a : ℕ) : ℝ) / W) + (((n - i + b : ℕ) : ℝ) / W) =
      (((n + (a + b) : ℕ) : ℝ) / W) := by
    rw [← add_div, ← Nat.cast_add]
    congr 2
    omega
  calc
    _ = ((n.choose i : ℝ) * P i * Q (n - i)) *
        (H ^ (((i + a : ℕ) : ℝ) / W) * H ^ (((n - i + b : ℕ) : ℝ) / W)) := by ring
    _ = _ := by rw [← Real.rpow_add hH, hexp]

/-- Primitive profiles propagate through a product without spending a full
high norm on either factor (`app:ch_regular_base:eq:actual-one-high`). -/
theorem transportLeibnizBound_profile_le {p q P Q : ℕ → ℝ}
    {H : ℝ} (hH : 0 < H) (W a b n : ℕ)
    (hp : ∀ k ≤ n, 0 ≤ p k) (hQ : ∀ k ≤ n, 0 ≤ Q k)
    (hpP : ∀ k ≤ n, p k ≤ P k * H ^ (((k + a : ℕ) : ℝ) / W))
    (hqQ : ∀ k ≤ n, q k ≤ Q k * H ^ (((k + b : ℕ) : ℝ) / W)) :
    transportLeibnizBound p q n ≤
      transportLeibnizBound P Q n * H ^ (((n + (a + b) : ℕ) : ℝ) / W) := by
  rw [← transportLeibnizBound_rpow P Q hH W a b n]
  exact transportLeibnizBound_mono hp
    (fun k hk ↦ mul_nonneg (hQ k hk) (Real.rpow_nonneg hH.le _)) hpP hqQ

/-- The final collapse spends one high norm only when the total shared budget
fits its index. The choice `W = s + β` has a shift independent of `s` in
`app:ch_regular_base:eq:actual-one-high`. -/
theorem transportProfile_le_oneHigh {H C : ℝ} (hH : 1 ≤ H) (hC : 0 ≤ C)
    {W k : ℕ} (hk : k ≤ W) : C * H ^ ((k : ℝ) / W) ≤ C * H := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_self_of_one_le hH
  by_cases hW : W = 0
  · simp [hW]
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hW)).mpr
      (by exact_mod_cast hk)

/-- Padding a fixed primitive shift does not enlarge the high coefficient
index by a multiple of the output order (`app:ch_regular_base:eq:actual-one-high`). -/
theorem transportProfile_mono_shift {H C : ℝ} (hH : 1 ≤ H) (hC : 0 ≤ C)
    (W n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    C * H ^ (((n + a : ℕ) : ℝ) / W) ≤
      C * H ^ (((n + b : ℕ) : ℝ) / W) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hH
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left hab n)
    (Nat.cast_nonneg _)

variable {ι : Type*} [Fintype ι]

/-- The constant for the two terms of the correction, independent of the high
norm (`app:ch_regular_base:eq:direct-graph-amplitudes`). -/
def correctionProfileConstant (M : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Fintype.card ι : ℝ) * transportLeibnizBound M M n +
    (1 / 2 : ℝ) * (Fintype.card ι : ℝ) ^ 2 *
      transportLeibnizBound M (transportLeibnizBound M M) n

/-- Nonnegativity of the correction's fixed profile constant. -/
theorem correctionProfileConstant_nonneg {M : ℕ → ℝ}
    (hM : ∀ k, 0 ≤ M k) (n : ℕ) : 0 ≤ correctionProfileConstant (ι := ι) M n := by
  unfold correctionProfileConstant
  have hp := transportLeibnizBound_nonneg hM hM
  have hq := transportLeibnizBound_nonneg hM hp n
  have hp' := hp n
  positivity

/-- Both correction terms obey a single exponent with fixed shift `3 * δ`.
The Hessian, covector jets and full matrix transport all share the derivative
budget (`app:ch_regular_base:eq:actual-one-high`). -/
theorem correctionDerivativeBound_profile_le
    {c1 dU : ι → ℕ → ℝ} {c2 S : ι → ι → ℕ → ℝ} {U M : ℕ → ℝ}
    {H : ℝ} (hH : 1 ≤ H) (hM : ∀ k, 0 ≤ M k) (W δ n : ℕ)
    (hc1 : ∀ j k, k ≤ n → 0 ≤ c1 j k ∧ c1 j k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdU : ∀ j k, k ≤ n → 0 ≤ dU j k ∧ dU j k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2 : ∀ j l k, k ≤ n → 0 ≤ c2 j l k ∧ c2 j l k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hS : ∀ j l k, k ≤ n → 0 ≤ S j l k ∧ S j l k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hU : ∀ k, k ≤ n → 0 ≤ U k ∧ U k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    correctionDerivativeBound c1 dU c2 S U n ≤
      correctionProfileConstant (ι := ι) M n * H ^ (((n + 3 * δ : ℕ) : ℝ) / W) := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hp := transportLeibnizBound_nonneg hM hM
  have hfirst (j : ι) : transportLeibnizBound (c1 j) (dU j) n ≤
      transportLeibnizBound M M n * H ^ (((n + 3 * δ : ℕ) : ℝ) / W) := by
    exact (transportLeibnizBound_profile_le hH0 W δ δ n
      (fun k hk ↦ (hc1 j k hk).1) (fun k _ ↦ hM k)
      (fun k hk ↦ (hc1 j k hk).2) (fun k hk ↦ (hdU j k hk).2)).trans
      (transportProfile_mono_shift hH (hp n) W n (by omega))
  have hinner (j l : ι) (k : ℕ) (hk : k ≤ n) :
      transportLeibnizBound (c2 j l) U k ≤
        transportLeibnizBound M M k * H ^ (((k + (δ + δ) : ℕ) : ℝ) / W) :=
    transportLeibnizBound_profile_le hH0 W δ δ k
      (fun q hq ↦ (hc2 j l q (hq.trans hk)).1) (fun q _ ↦ hM q)
      (fun q hq ↦ (hc2 j l q (hq.trans hk)).2)
      (fun q hq ↦ (hU q (hq.trans hk)).2)
  have hsecond (j l : ι) :
      transportLeibnizBound (S j l) (transportLeibnizBound (c2 j l) U) n ≤
        transportLeibnizBound M (transportLeibnizBound M M) n *
          H ^ (((n + 3 * δ : ℕ) : ℝ) / W) := by
    simpa only [show δ + (δ + δ) = 3 * δ by omega] using
      transportLeibnizBound_profile_le hH0 W δ (δ + δ) n
        (fun k hk ↦ (hS j l k hk).1) (fun k _ ↦ hp k)
        (fun k hk ↦ (hS j l k hk).2) (hinner j l)
  calc
    _ ≤ (∑ j : ι, transportLeibnizBound M M n * H ^ (((n + 3 * δ : ℕ) : ℝ) / W)) +
        (1 / 2 : ℝ) * ∑ _j : ι, ∑ _l : ι,
          transportLeibnizBound M (transportLeibnizBound M M) n *
            H ^ (((n + 3 * δ : ℕ) : ℝ) / W) := by
      exact add_le_add (Finset.sum_le_sum fun j _ ↦ hfirst j)
        (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun l _ ↦ hsecond j l)
          (by norm_num))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, correctionProfileConstant]
      ring

/-- The constant for the complete remainder's primitive derivative bound,
including `B b₋₁`, in `app:ch_regular_base:eq:direct-graph-identity`. -/
def completeRemainderProfileConstant (M : ℕ → ℝ) (V : ι → ℝ) (n : ℕ) : ℝ :=
  (∑ j, transportLeibnizBound M
    (fun k ↦ V j * correctionProfileConstant (ι := ι) M (k + 1)) n) +
    transportLeibnizBound M (correctionProfileConstant (ι := ι) M) n

/-- Nonnegativity of the complete remainder's profile constant. -/
theorem completeRemainderProfileConstant_nonneg {M : ℕ → ℝ} {V : ι → ℝ}
    (hM : ∀ k, 0 ≤ M k) (hV : ∀ j, 0 ≤ V j) (n : ℕ) :
    0 ≤ completeRemainderProfileConstant M V n := by
  have hC := correctionProfileConstant_nonneg (ι := ι) hM
  exact add_nonneg (Finset.sum_nonneg fun j _ ↦
    transportLeibnizBound_nonneg hM (fun k ↦ mul_nonneg (hV j) (hC (k + 1))) n)
    (transportLeibnizBound_nonneg hM hC n)

/-- The full primitive budget for the remainder has exponent `n + 4 * δ + 1`.
The `+1` is the actual physical derivative of the correction. This is the
one-high algebra needed by `norm_iteratedFDeriv_completeTransportRemainder_le`
in `app:ch_regular_base:eq:actual-one-high`, without an assumed correction or
remainder estimate. -/
theorem completeTransportDerivativeBound_profile_le
    {A c1 dU : ι → ℕ → ℝ} {c2 S : ι → ι → ℕ → ℝ}
    {B U M : ℕ → ℝ} {V : ι → ℝ}
    {H : ℝ} (hH : 1 ≤ H) (hM : ∀ k, 0 ≤ M k) (hV : ∀ j, 0 ≤ V j)
    (W δ n : ℕ)
    (hA : ∀ j k, k ≤ n → 0 ≤ A j k ∧ A j k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hB : ∀ k, k ≤ n → 0 ≤ B k ∧ B k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc1 : ∀ j k, k ≤ n + 1 → 0 ≤ c1 j k ∧ c1 j k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hdU : ∀ j k, k ≤ n + 1 → 0 ≤ dU j k ∧ dU j k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hc2 : ∀ j l k, k ≤ n + 1 → 0 ≤ c2 j l k ∧ c2 j l k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hS : ∀ j l k, k ≤ n + 1 → 0 ≤ S j l k ∧ S j l k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hU : ∀ k, k ≤ n + 1 → 0 ≤ U k ∧ U k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W)) :
    let Q := correctionDerivativeBound c1 dU c2 S U
    (∑ j, transportLeibnizBound (A j) (fun k ↦ V j * Q (k + 1)) n) +
        transportLeibnizBound B Q n ≤
      completeRemainderProfileConstant M V n * H ^ (((n + (4 * δ + 1) : ℕ) : ℝ) / W) := by
  intro Q
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hC := correctionProfileConstant_nonneg (ι := ι) hM
  have hQ (k : ℕ) (hk : k ≤ n + 1) : Q k ≤
      correctionProfileConstant (ι := ι) M k * H ^ (((k + 3 * δ : ℕ) : ℝ) / W) :=
    correctionDerivativeBound_profile_le hH hM W δ k
      (fun j q hq ↦ hc1 j q (hq.trans hk)) (fun j q hq ↦ hdU j q (hq.trans hk))
      (fun j l q hq ↦ hc2 j l q (hq.trans hk))
      (fun j l q hq ↦ hS j l q (hq.trans hk)) (fun q hq ↦ hU q (hq.trans hk))
  have hfirst (j : ι) : transportLeibnizBound (A j) (fun k ↦ V j * Q (k + 1)) n ≤
      transportLeibnizBound M
        (fun k ↦ V j * correctionProfileConstant (ι := ι) M (k + 1)) n *
          H ^ (((n + (4 * δ + 1) : ℕ) : ℝ) / W) := by
    have hright (k : ℕ) (hk : k ≤ n) : V j * Q (k + 1) ≤
        (V j * correctionProfileConstant (ι := ι) M (k + 1)) *
          H ^ (((k + (3 * δ + 1) : ℕ) : ℝ) / W) := by
      simpa only [mul_assoc, show k + 1 + 3 * δ = k + (3 * δ + 1) by omega] using
        mul_le_mul_of_nonneg_left (hQ (k + 1) (by omega)) (hV j)
    simpa only [show δ + (3 * δ + 1) = 4 * δ + 1 by omega] using
      transportLeibnizBound_profile_le hH0 W δ (3 * δ + 1) n
        (fun k hk ↦ (hA j k hk).1) (fun k _ ↦ mul_nonneg (hV j) (hC (k + 1)))
        (fun k hk ↦ (hA j k hk).2) hright
  have hsecond : transportLeibnizBound B Q n ≤
      transportLeibnizBound M (correctionProfileConstant (ι := ι) M) n *
        H ^ (((n + (4 * δ + 1) : ℕ) : ℝ) / W) := by
    exact (transportLeibnizBound_profile_le hH0 W δ (3 * δ) n
      (fun k hk ↦ (hB k hk).1) (fun k _ ↦ hC k)
      (fun k hk ↦ (hB k hk).2) (fun k hk ↦ hQ k (by omega))).trans
      (transportProfile_mono_shift hH (transportLeibnizBound_nonneg hM hC n) W n (by omega))
  exact (add_le_add (Finset.sum_le_sum fun j _ ↦ hfirst j) hsecond).trans_eq
    (by simp only [completeRemainderProfileConstant, add_mul, Finset.sum_mul])

/-- A primitive's fixed jet shift is charged above its fixed low baseline.
This converts the project's joint-budget interpolation input into the profile
used above; neither the baseline nor the shift depends on the output order.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
theorem transportPrimitiveProfile_of_interpolation
    (a : ℕ → ℝ) (b σ δ W k : ℕ) (B K H : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hmono : Monotone a)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : a b ≤ B) (hhigh : a (b + W) ≤ H)
    (hshift : σ ≤ b + δ) (hk : k + δ ≤ W)
    (hinterp : b < k + σ → k + σ < b + W →
      a (k + σ) ≤ K * a b ^ (1 - ((k + σ - b : ℕ) : ℝ) / W) *
        a (b + W) ^ (((k + σ - b : ℕ) : ℝ) / W)) :
    a (k + σ) ≤ (K * B) * H ^ (((k + δ : ℕ) : ℝ) / W) := by
  apply (JointBudget.interpolation_le_scaled_rpow a b W (k + σ) B K H
    ha hmono hB hK hH hlow hhigh (by omega) hinterp).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hB))
  apply Real.rpow_le_rpow_of_exponent_le hH
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast (show k + σ - b ≤ k + δ by omega)) (Nat.cast_nonneg _)

/-- Three fixed masks add only their three fixed primitive shifts. This is
the scalar budget consumed by `norm_iteratedFDeriv_maskedTransportAmplitude_le`
in `app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem maskedTransportDerivativeBound_profile_le
    {t s g b M C : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (hM : ∀ k, 0 ≤ M k) (hC : ∀ k, 0 ≤ C k) (W δ d n : ℕ)
    (ht : ∀ k ≤ n, 0 ≤ t k ∧ t k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hs : ∀ k ≤ n, 0 ≤ s k ∧ s k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hg : ∀ k ≤ n, 0 ≤ g k ∧ g k ≤ M k * H ^ (((k + δ : ℕ) : ℝ) / W))
    (hb : ∀ k ≤ n, b k ≤ C k * H ^ (((k + d : ℕ) : ℝ) / W)) :
    transportLeibnizBound t (transportLeibnizBound s (transportLeibnizBound g b)) n ≤
      transportLeibnizBound M (transportLeibnizBound M (transportLeibnizBound M C)) n *
        H ^ (((n + (3 * δ + d) : ℕ) : ℝ) / W) := by
  have hMC := transportLeibnizBound_nonneg hM hC
  have hMMC := transportLeibnizBound_nonneg hM hMC
  have hgb (k : ℕ) (hk : k ≤ n) :=
    transportLeibnizBound_profile_le hH W δ d k
      (fun q hq ↦ (hg q (hq.trans hk)).1) (fun q _ ↦ hC q)
      (fun q hq ↦ (hg q (hq.trans hk)).2) (fun q hq ↦ hb q (hq.trans hk))
  have hsgb (k : ℕ) (hk : k ≤ n) :=
    transportLeibnizBound_profile_le hH W δ (δ + d) k
      (fun q hq ↦ (hs q (hq.trans hk)).1) (fun q _ ↦ hMC q)
      (fun q hq ↦ (hs q (hq.trans hk)).2) (fun q hq ↦ hgb q (hq.trans hk))
  simpa only [show δ + (δ + (δ + d)) = 3 * δ + d by omega] using
    transportLeibnizBound_profile_le hH W δ (δ + (δ + d)) n
      (fun q hq ↦ (ht q hq).1) (fun q _ ↦ hMMC q)
      (fun q hq ↦ (ht q hq).2) hsgb

end JanetCartan.FourierIntegral
